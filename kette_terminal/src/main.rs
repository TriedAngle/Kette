use kette::PRELOAD;
use kette::VM;

use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use ratatui::layout::Rect;
use ratatui::{
    backend::{Backend, CrosstermBackend},
    layout::{Constraint, Direction, Layout},
    style::{Color, Modifier, Style},
    text::{Line, Span, Text},
    widgets::{
        Block, Borders, List, ListItem, ListState, Paragraph, ScrollDirection, Scrollbar,
        ScrollbarOrientation, ScrollbarState,
    },
    Frame, Terminal,
};
use std::{error::Error, io};
use tui_input::backend::crossterm::EventHandler;
use tui_input::Input;
enum InputMode {
    Normal,
    Editing,
}

struct App {
    input: Input,
    input_mode: InputMode,
    messages: Vec<String>,
    list: ListState,
}

impl Default for App {
    fn default() -> App {
        App {
            input: Input::default(),
            input_mode: InputMode::Normal,
            messages: Vec::new(),
            list: ListState::default(),
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    // let mut vm = VM::new();
    // vm.init();
    // unsafe {
    //     let preload =  vm.compile_string(PRELOAD);
    //     vm.execute_quotation(preload.as_quotation());
    // }

    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let app = App::default();
    let res = run_app(&mut terminal, app);

    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )?;
    terminal.show_cursor()?;

    Ok(())

    // vm.deinit();
}

fn run_app<B: Backend>(terminal: &mut Terminal<B>, mut app: App) -> io::Result<()> {
    loop {
        terminal.draw(|f| ui(f, &mut app))?;

        if let Event::Key(key) = event::read()? {
            match app.input_mode {
                InputMode::Normal => match key.code {
                    KeyCode::Char('e') => {
                        app.input_mode = InputMode::Editing;
                    }
                    KeyCode::Char('q') => {
                        return Ok(());
                    }
                    KeyCode::Up => {
                        let i = match app.list.selected() {
                            Some(i) => {
                                if i > 0 {
                                    i - 1
                                } else {
                                    i
                                }
                            }
                            None => 0,
                        };
                        app.list.select(Some(i));
                    }
                    KeyCode::Down => {
                        let i = match app.list.selected() {
                            Some(i) => {
                                if i < app.messages.len() - 1 {
                                    i + 1
                                } else {
                                    i
                                }
                            }
                            None => 0,
                        };
                        app.list.select(Some(i));
                    }
                    _ => {}
                },
                InputMode::Editing => match (key.code, key.modifiers) {
                    (KeyCode::Char('N'), event::KeyModifiers::SHIFT) => {
                        let mut current_value = app.input.value().to_string();
                        current_value.push('\n');
                        app.input = app.input.with_value(current_value);
                    }
                    (KeyCode::Enter, s) => {
                        app.messages.push(app.input.value().into());
                        app.input.reset();
                        app.list.select(Some(app.messages.len() - 1));
                        app.input_mode = InputMode::Normal;
                    }
                    (KeyCode::Esc, _) => {
                        app.input_mode = InputMode::Normal;
                    }
                    _ => {
                        app.input.handle_event(&Event::Key(key));
                    }
                },
            }
        }
    }
}

fn ui(f: &mut Frame, app: &mut App) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(2)
        .constraints([
            Constraint::Percentage(70),
            Constraint::Min(1),
            Constraint::Length(1),
        ])
        .split(f.size());

    let (msg, style) = match app.input_mode {
        InputMode::Normal => (
            vec![
                Span::raw("Press "),
                Span::styled("q", Style::default().add_modifier(Modifier::BOLD)),
                Span::raw(" to exit, "),
                Span::styled("e", Style::default().add_modifier(Modifier::BOLD)),
                Span::raw(" to start editing."),
            ],
            Style::default().add_modifier(Modifier::RAPID_BLINK),
        ),
        InputMode::Editing => (
            vec![
                Span::raw("Press "),
                Span::styled("Esc", Style::default().add_modifier(Modifier::BOLD)),
                Span::raw(" to stop editing, "),
                Span::styled("Enter", Style::default().add_modifier(Modifier::BOLD)),
                Span::raw(" to record the message"),
            ],
            Style::default(),
        ),
    };

    // Message history
    let messages: Vec<ListItem> = app
        .messages
        .iter()
        .map(|m| ListItem::new(Span::raw(m)))
        .collect();
    let messages_list = List::new(messages)
        .block(
            Block::default()
                .borders(Borders::ALL)
                .title("Message History"),
        )
        .highlight_style(Style::default().add_modifier(Modifier::BOLD))
        .highlight_symbol("> ");
    f.render_stateful_widget(messages_list, chunks[0], &mut app.list);

    let text = Text::from(Line::from(msg)).style(style);
    let help_message = Paragraph::new(text);
    f.render_widget(help_message, chunks[2]);

    let width = chunks[0].width.max(3) - 3; // keep 2 for borders and 1 for cursor
    let height = chunks[2].height - 2; // minus borders

    let (line, column, horizontal_scroll, vertical_scroll) = calculate_scroll_offsets(
        app.input.value(),
        app.input.cursor(),
        width as usize,
        height as usize,
    );
    let input = Paragraph::new(app.input.value())
        .style(match app.input_mode {
            InputMode::Normal => Style::default(),
            InputMode::Editing => Style::default().fg(Color::Yellow),
        })
        .scroll((vertical_scroll as u16, horizontal_scroll as u16))
        .block(Block::default().borders(Borders::ALL).title("Input"));
    f.render_widget(input, chunks[1]);

    match app.input_mode {
        InputMode::Normal =>
            // Hide the cursor. `Frame` does this by default, so we don't need to do anything here
            {}

        InputMode::Editing => {
            // Make the cursor visible and ask tui-rs to put it at the specified coordinates after rendering
            f.set_cursor(
                // Put cursor past the end of the input text
                chunks[2].x + (column - horizontal_scroll) as u16 + 1,
                chunks[2].y + (line - vertical_scroll) as u16 + 1,
            )
        }
    }
}

fn calculate_scroll_offsets(
    input: &str,
    cursor_pos: usize,
    width: usize,
    height: usize,
) -> (usize, usize, usize, usize) {
    let mut accumulated_length = 0;
    let mut line = 0;
    let mut column = 0;
    let mut visible_top_line = 0;

    let lines: Vec<&str> = input.split('\n').collect();
    for line_str in &lines {
        let line_length = line_str.chars().count();
        if accumulated_length + line_length >= cursor_pos {
            column = cursor_pos - accumulated_length;
            if line >= height {
                visible_top_line = line - height + 1; // Adjust the top visible line to keep the cursor in view
            }
            break;
        }
        accumulated_length += line_length + 1; // +1 for the newline character
        line += 1;
    }

    // Calculate horizontal scrolling based on width
    let horizontal_scroll = if column > width { column - width } else { 0 };

    (line, column, horizontal_scroll, visible_top_line)
}
