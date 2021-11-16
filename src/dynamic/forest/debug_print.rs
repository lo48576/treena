//! Debug printer.

use core::fmt::{self, Write as _};

use alloc::vec::Vec;

use crate::dynamic::forest::Node;
use crate::dynamic::hierarchy::traverse::{DepthFirstTraverser, DftEvent};
use crate::dynamic::hierarchy::Hierarchy;
use crate::dynamic::{InternalNodeId, NodeId};

/// State for an indent level.
#[derive(Clone, Copy)]
struct IndentLevel {
    /// Whether this is the last item.
    is_last_item: bool,
    /// Whether the line is the first line.
    is_first_line: bool,
}

impl IndentLevel {
    /// Returns the indent string for the indent type.
    fn as_str(self) -> &'static str {
        match (self.is_last_item, self.is_first_line) {
            (false, true) => "|-- ",
            (false, false) => "|   ",
            (true, true) => "`-- ",
            (true, false) => "    ",
        }
    }

    /// Returns the leading part of the indent string.
    fn as_str_leading(self) -> &'static str {
        match (self.is_last_item, self.is_first_line) {
            (false, true) => "|--",
            (false, false) => "|",
            (true, true) => "`--",
            (true, false) => "",
        }
    }

    /// Returns the trailing whitespaces part of the indent string.
    fn as_str_trailing_spaces(self) -> &'static str {
        match (self.is_last_item, self.is_first_line) {
            (_, true) => " ",
            (false, false) => "   ",
            (true, false) => "    ",
        }
    }

    /// Returns whether the indent string consists of only whitespaces.
    #[inline]
    #[must_use]
    fn is_all_whitespace(&self) -> bool {
        self.is_last_item && !self.is_first_line
    }
}

/// State of the line writing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LineState {
    /// Before any character of the indent is written to the current line.
    BeforeIndent,
    /// Indents are partially written.
    ///
    /// More precisely, trailing whitespaces are not yet written.
    PartialIndent,
    /// Writing content.
    Content,
}

/// Indent writer for the debug printer.
struct IndentWriter<'a, 'b> {
    /// Backend formatter.
    fmt: &'b mut fmt::Formatter<'a>,
    /// State of the line writing.
    line_state: LineState,
    /// Indents.
    indents: Vec<IndentLevel>,
}

impl<'a, 'b> IndentWriter<'a, 'b> {
    /// Creates a new `PadAdapter`.
    fn new(fmt: &'b mut fmt::Formatter<'a>) -> Self {
        Self {
            fmt,
            line_state: LineState::BeforeIndent,
            indents: Vec::new(),
        }
    }

    /// Opens the next item.
    ///
    /// Writes a newline if necessary and prepares to write the next item.
    ///
    /// This should **not** be called for the root item.
    fn open_item(&mut self, is_last_item: bool) -> fmt::Result {
        if self.line_state != LineState::BeforeIndent {
            self.fmt.write_char('\n')?;
            self.line_state = LineState::BeforeIndent;
        }
        if let Some(indent) = self.indents.last_mut() {
            indent.is_first_line = false;
        }
        self.indents.push(IndentLevel {
            is_last_item,
            is_first_line: true,
        });

        Ok(())
    }

    /// Closes the current item.
    ///
    /// Returns `Ok(())` if an item is successfully closed.
    /// Returns `Err(())` if there are no items that can be closed, i.e. the
    /// current item is the root.
    fn close_item(&mut self) -> Result<(), ()> {
        match self.indents.pop() {
            Some(_) => Ok(()),
            None => Err(()),
        }
    }

    /// Writes the indent except for the trailing whitespaces.
    fn write_indent_partial(&mut self) -> fmt::Result {
        let mut indents = &self.indents[..];
        while indents.last().map_or(false, |i| i.is_all_whitespace()) {
            indents = &indents[..(indents.len() - 1)];
        }
        if let Some(last) = indents.last() {
            for indent in &indents[..(indents.len() - 1)] {
                self.fmt.write_str(indent.as_str())?;
            }
            self.fmt.write_str(last.as_str_leading())?;
        }

        Ok(())
    }

    /// Writes the rest of the indents which are partially written.
    fn complete_partial_indent(&mut self) -> fmt::Result {
        debug_assert_eq!(self.line_state, LineState::PartialIndent);
        if let Some(indent) = self.indents.last() {
            self.fmt.write_str(indent.as_str_trailing_spaces())?;
        }

        Ok(())
    }
}

impl fmt::Write for IndentWriter<'_, '_> {
    fn write_str(&mut self, mut s: &str) -> fmt::Result {
        while !s.is_empty() {
            // There remains something to print.

            if self.line_state == LineState::BeforeIndent {
                self.write_indent_partial()?;
                self.line_state = LineState::PartialIndent;
            }

            let (line_end, ends_with_newline) = match s.find('\n') {
                Some(pos) => {
                    if let Some(level) = self.indents.last_mut() {
                        level.is_first_line = false;
                    }
                    (pos + 1, true)
                }
                None => (s.len(), false),
            };
            let content = &s[..line_end];
            if !content.is_empty() {
                debug_assert_ne!(
                    self.line_state,
                    LineState::BeforeIndent,
                    "[consistency] indent must be written since there are something to write"
                );
                if self.line_state == LineState::PartialIndent {
                    self.complete_partial_indent()?;
                }
                self.fmt.write_str(content)?;

                self.line_state = if ends_with_newline {
                    LineState::BeforeIndent
                } else {
                    LineState::Content
                };
            }
            s = &s[line_end..];
        }

        Ok(())
    }
}

/// Tree printer for debugging.
///
/// This is provided mainly for debugging purpose. Node that the output format
/// is not guaranteed to be stable, and any format changes won't be considered
/// as breaking changes.
#[cfg_attr(feature = "docsrs", doc(cfg(feature = "debug-print")))]
pub struct DebugPrint<'a, Id: NodeId, T> {
    /// Root node of the (sub)tree to print.
    node: Node<'a, Id, T>,
}

impl<'a, Id: NodeId, T> DebugPrint<'a, Id, T> {
    /// Creates a new `DebugPrint` object for the node.
    pub(crate) fn new(node: Node<'a, Id, T>) -> Self {
        Self { node }
    }
}

impl<'a, Id: NodeId, T: fmt::Display> fmt::Display for DebugPrint<'a, Id, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        /// Implementation that depends on `Id::Internal` instead of `NodeId`
        /// in order to reduce monomorphization and prevent binary bloat.
        fn inner<InternalId: InternalNodeId, T: fmt::Display>(
            writer: &mut IndentWriter<'_, '_>,
            hierarchy: &Hierarchy<InternalId>,
            data: &[Option<T>],
            root: InternalId,
        ) -> fmt::Result {
            let mut traverser = DepthFirstTraverser::with_toplevel(root, hierarchy);

            // Print the first (root) node.
            traverser.next(hierarchy);
            let root_data = data[root.to_usize()]
                .as_ref()
                .expect("[consistency] the node must have a data when alive");
            write!(writer, "{}", root_data)?;

            // Print descendants.
            while let Some(id) = prepare_next_node_printing(writer, hierarchy, &mut traverser)? {
                let node_data = data[id.to_usize()]
                    .as_ref()
                    .expect("[consistency] the node must have a data when alive");
                write!(writer, "{}", node_data)?;
            }
            assert!(traverser.next(hierarchy).is_none());

            Ok(())
        }

        let mut writer = IndentWriter::new(f);
        let hierarchy = &self.node.forest().hierarchy;
        let data = &self.node.forest().data;
        let id = self.node.id().to_internal();

        inner(&mut writer, hierarchy, data, id)
    }
}

impl<'a, Id: NodeId, T: fmt::Debug> fmt::Debug for DebugPrint<'a, Id, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        /// Implementation that depends on `Id::Internal` instead of `NodeId`
        /// in order to reduce monomorphization and prevent binary bloat.
        fn inner<InternalId: InternalNodeId, T: fmt::Debug>(
            writer: &mut IndentWriter<'_, '_>,
            hierarchy: &Hierarchy<InternalId>,
            data: &[Option<T>],
            root: InternalId,
        ) -> fmt::Result {
            let mut traverser = DepthFirstTraverser::with_toplevel(root, hierarchy);

            // Print the first (root) node.
            traverser.next(hierarchy);
            let root_data = data[root.to_usize()]
                .as_ref()
                .expect("[consistency] the node must have a data when alive");
            write!(writer, "{:?}", root_data)?;

            // Print descendants.
            while let Some(id) = prepare_next_node_printing(writer, hierarchy, &mut traverser)? {
                let node_data = data[id.to_usize()]
                    .as_ref()
                    .expect("[consistency] the node must have a data when alive");
                write!(writer, "{:?}", node_data)?;
            }
            assert!(traverser.next(hierarchy).is_none());

            Ok(())
        }

        let mut writer = IndentWriter::new(f);
        let hierarchy = &self.node.forest().hierarchy;
        let data = &self.node.forest().data;
        let id = self.node.id().to_internal();

        inner(&mut writer, hierarchy, data, id)
    }
}

/// Prepares printing of next node.
///
/// Internally, this searches next node open and adjust indent level and prefix.
fn prepare_next_node_printing<Id: InternalNodeId>(
    writer: &mut IndentWriter<'_, '_>,
    hierarchy: &Hierarchy<Id>,
    traverser: &mut DepthFirstTraverser<Id>,
) -> Result<Option<Id>, fmt::Error> {
    while let Some(ev) = traverser.next(hierarchy) {
        let open_id = match ev {
            DftEvent::Open(id) => id,
            DftEvent::Close(_) => {
                if writer.close_item().is_ok() {
                    continue;
                } else {
                    break;
                }
            }
        };
        let is_last_sibling = hierarchy
            .neighbors(open_id)
            .expect("[consistency] the node being traversed must be alive")
            .next_sibling()
            .is_none();
        writer.open_item(is_last_sibling)?;

        return Ok(Some(open_id));
    }

    Ok(None)
}
