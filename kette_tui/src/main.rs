use clap::Parser as ClapParser;
use crossterm::{
    event::{self, Event, KeyCode, KeyModifiers},
    execute,
    terminal::{
        EnterAlternateScreen, LeaveAlternateScreen, disable_raw_mode,
        enable_raw_mode,
    },
};
use kette::{
    Allocator, Array, BytecodeCompiler, ExecutionResult, ExecutionState,
    ExecutionStateInfo, Handle, HeapSettings, Instruction, Interpreter, OpCode,
    Parser, Tagged, ThreadProxy, VM, VMCreateInfo, VMThread,
};
use ratatui::{
    Terminal,
    backend::CrosstermBackend,
    layout::{Alignment, Constraint, Direction, Layout, Rect},
    style::{Color, Modifier, Style, Stylize},
    text::{Line, Span},
    widgets::{
        Block, Borders, Clear, List, ListItem, ListState, Paragraph, Wrap,
    },
};
use std::{
    env,
    fs::{self, File},
    io,
    path::PathBuf,
    sync::{Arc, Mutex},
};

#[derive(ClapParser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[arg(required = false)]
    files: Vec<String>,
}

#[derive(PartialEq)]
enum PopupFocus {
    PathInput,
    FileBrowser,
}

#[derive(Clone)]
struct OutputCapture {
    buffer: Arc<Mutex<Vec<u8>>>,
}

impl OutputCapture {
    fn new() -> Self {
        Self {
            buffer: Arc::new(Mutex::new(Vec::new())),
        }
    }

    fn get_string(&self) -> String {
        let data = self.buffer.lock().unwrap();
        String::from_utf8_lossy(&data).to_string()
    }
}

impl io::Write for OutputCapture {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let mut data = self.buffer.lock().unwrap();
        data.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

struct App {
    messages: Vec<Line<'static>>,
    input: Vec<String>,
    cursor: (usize, usize),
    history: Vec<Vec<String>>,
    history_index: Option<usize>,
    draft: Vec<String>,
    scroll: u16,

    show_file_popup: bool,
    popup_focus: PopupFocus,
    popup_path_input: String,
    popup_cursor_x: usize,
    popup_entries: Vec<(String, bool)>,
    popup_list_state: ListState,
    current_browser_path: PathBuf,
}

impl App {
    fn new() -> Self {
        let current_dir =
            env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let mut app = Self {
            messages: vec![Line::from(vec![Span::styled(
                "Kette REPL",
                Style::default().add_modifier(Modifier::BOLD),
            )])],
            input: vec![String::new()],
            cursor: (0, 0),
            history: Vec::new(),
            history_index: None,
            draft: vec![String::new()],
            scroll: 0,

            show_file_popup: false,
            popup_focus: PopupFocus::FileBrowser,
            popup_path_input: current_dir.to_string_lossy().to_string(),
            popup_cursor_x: current_dir.to_string_lossy().len(),
            popup_entries: Vec::new(),
            popup_list_state: ListState::default(),
            current_browser_path: current_dir,
        };
        app.refresh_file_list();
        app
    }

    fn add_message(&mut self, msg: Line<'static>) {
        self.messages.push(msg);
    }

    fn add_error(&mut self, err: String) {
        self.messages.push(Line::from(Span::styled(
            err,
            Style::default().fg(Color::Red),
        )));
    }

    fn add_system_msg(&mut self, msg: String) {
        self.messages.push(Line::from(Span::styled(
            msg,
            Style::default()
                .fg(Color::Yellow)
                .add_modifier(Modifier::ITALIC),
        )));
    }

    fn submit_input(&mut self) -> String {
        let text = self.input.join("\n");
        for (i, line) in self.input.iter().enumerate() {
            let prefix = if i == 0 { "> " } else { ". " };
            self.messages.push(Line::from(vec![
                Span::styled(prefix, Style::default().fg(Color::Green)),
                Span::raw(line.clone()),
            ]));
        }

        if !text.trim().is_empty() {
            self.history.push(self.input.clone());
        }

        self.input = vec![String::new()];
        self.cursor = (0, 0);
        self.history_index = None;
        self.draft = vec![String::new()];
        self.scroll = self.messages.len() as u16;
        text
    }

    fn insert_char(&mut self, c: char) {
        let line = &mut self.input[self.cursor.0];
        if self.cursor.1 >= line.len() {
            line.push(c);
        } else {
            line.insert(self.cursor.1, c);
        }
        self.cursor.1 += 1;
    }

    fn insert_newline(&mut self) {
        let current_line = &mut self.input[self.cursor.0];
        let rest = current_line.split_off(self.cursor.1);
        self.input.insert(self.cursor.0 + 1, rest);
        self.cursor.0 += 1;
        self.cursor.1 = 0;
    }

    fn delete_char(&mut self) {
        if self.cursor.1 > 0 {
            let line = &mut self.input[self.cursor.0];
            line.remove(self.cursor.1 - 1);
            self.cursor.1 -= 1;
        } else if self.cursor.0 > 0 {
            let current_line = self.input.remove(self.cursor.0);
            self.cursor.0 -= 1;
            let prev_line = &mut self.input[self.cursor.0];
            self.cursor.1 = prev_line.len();
            prev_line.push_str(&current_line);
        }
    }

    fn move_cursor_left(&mut self) {
        if self.cursor.1 > 0 {
            self.cursor.1 -= 1;
        } else if self.cursor.0 > 0 {
            self.cursor.0 -= 1;
            self.cursor.1 = self.input[self.cursor.0].len();
        }
    }

    fn move_cursor_right(&mut self) {
        if self.cursor.1 < self.input[self.cursor.0].len() {
            self.cursor.1 += 1;
        } else if self.cursor.0 < self.input.len() - 1 {
            self.cursor.0 += 1;
            self.cursor.1 = 0;
        }
    }

    fn move_up(&mut self) {
        if self.cursor.0 > 0 {
            self.cursor.0 -= 1;
            self.cursor.1 = self.cursor.1.min(self.input[self.cursor.0].len());
        } else {
            self.history_back();
        }
    }

    fn move_down(&mut self) {
        if self.cursor.0 < self.input.len() - 1 {
            self.cursor.0 += 1;
            self.cursor.1 = self.cursor.1.min(self.input[self.cursor.0].len());
        } else {
            self.history_forward();
        }
    }

    fn history_back(&mut self) {
        if self.history.is_empty() {
            return;
        }
        if self.history_index.is_none() {
            self.draft = self.input.clone();
            self.history_index = Some(self.history.len());
        }
        if let Some(idx) = self.history_index {
            if idx > 0 {
                let new_idx = idx - 1;
                self.history_index = Some(new_idx);
                self.input = self.history[new_idx].clone();
                self.cursor.0 = self.input.len().saturating_sub(1);
                self.cursor.1 = self.input[self.cursor.0].len();
            }
        }
    }

    fn history_forward(&mut self) {
        if let Some(idx) = self.history_index {
            if idx + 1 < self.history.len() {
                let new_idx = idx + 1;
                self.history_index = Some(new_idx);
                self.input = self.history[new_idx].clone();
            } else {
                self.history_index = None;
                self.input = self.draft.clone();
            }
            self.cursor.0 = self.input.len().saturating_sub(1);
            self.cursor.1 = self.input[self.cursor.0].len();
        }
    }

    // --- File Browser Logic ---
    fn toggle_popup(&mut self) {
        self.show_file_popup = !self.show_file_popup;
        if self.show_file_popup {
            let current_dir =
                env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
            self.navigate_to(current_dir);
            self.popup_focus = PopupFocus::FileBrowser;
        }
    }

    fn refresh_file_list(&mut self) {
        self.popup_entries.clear();
        if let Ok(entries) = fs::read_dir(&self.current_browser_path) {
            let mut dirs = Vec::new();
            let mut files = Vec::new();

            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().to_string();
                if name.starts_with('.') {
                    continue;
                }
                if let Ok(ft) = entry.file_type() {
                    if ft.is_dir() {
                        dirs.push((name, true));
                    } else {
                        files.push((name, false));
                    }
                }
            }
            dirs.sort_by(|a, b| a.0.cmp(&b.0));
            files.sort_by(|a, b| a.0.cmp(&b.0));
            self.popup_entries.append(&mut dirs);
            self.popup_entries.append(&mut files);
        }
        self.popup_list_state.select(Some(0));
    }

    fn navigate_to(&mut self, path: PathBuf) {
        if let Ok(p) = path.canonicalize() {
            self.current_browser_path = p;
        } else {
            self.current_browser_path = path;
        }
        self.popup_path_input =
            self.current_browser_path.to_string_lossy().to_string();
        self.popup_cursor_x = self.popup_path_input.len();
        self.refresh_file_list();
    }

    fn popup_list_up(&mut self) {
        let i = match self.popup_list_state.selected() {
            Some(i) => {
                if i == 0 {
                    self.popup_entries.len().saturating_sub(1)
                } else {
                    i - 1
                }
            }
            None => 0,
        };
        self.popup_list_state.select(Some(i));
    }

    fn popup_list_down(&mut self) {
        let i = match self.popup_list_state.selected() {
            Some(i) => {
                if i >= self.popup_entries.len().saturating_sub(1) {
                    0
                } else {
                    i + 1
                }
            }
            None => 0,
        };
        self.popup_list_state.select(Some(i));
    }

    fn popup_list_enter(&mut self) -> Option<String> {
        if self.popup_entries.is_empty() {
            return None;
        }
        let index = self.popup_list_state.selected().unwrap_or(0);
        if index >= self.popup_entries.len() {
            return None;
        }

        let (name, is_dir) = &self.popup_entries[index];
        let new_path = self.current_browser_path.join(name);

        if *is_dir {
            self.navigate_to(new_path);
            None
        } else {
            Some(new_path.to_string_lossy().to_string())
        }
    }

    fn popup_list_back(&mut self) {
        if let Some(parent) = self.current_browser_path.parent() {
            self.navigate_to(parent.to_path_buf());
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    let file = File::create("kette_repl.log")
        .unwrap_or_else(|_| File::create("repl.log").unwrap());
    tracing_subscriber::fmt()
        .with_writer(Mutex::new(file))
        .with_ansi(false)
        .init();

    let vm = VM::new(VMCreateInfo {
        image: None,
        heap: HeapSettings::default(),
    });
    let main_proxy = vm.proxy();
    let heap = main_proxy.shared.heap.proxy();
    let state = ExecutionState::new(&ExecutionStateInfo {
        stack_size: 128,
        return_stack_size: 128,
    });
    let main_thread = VMThread::new_main();
    let thread_proxy = ThreadProxy(main_thread.inner);
    let proxy = vm.proxy();
    let mut interpreter = Interpreter::new(proxy, thread_proxy, heap, state);

    run_tui_repl(&mut interpreter, cli.files)?;

    Ok(())
}

fn run_tui_repl(
    interpreter: &mut Interpreter,
    startup_files: Vec<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let mut app = App::new();

    for filename in startup_files {
        app.add_system_msg(format!("Loading startup file: {}", filename));
        match fs::read_to_string(&filename) {
            Ok(source) => {
                run_interpreter_step(interpreter, &mut app, &source);
            }
            Err(e) => {
                app.add_error(format!("Failed to load {}: {}", filename, e));
            }
        }
    }

    terminal.draw(|f| ui(f, &mut app))?;

    loop {
        terminal.draw(|f| ui(f, &mut app))?;

        if let Event::Key(key) = event::read()? {
            if app.show_file_popup {
                match key.code {
                    KeyCode::Tab => {
                        app.popup_focus = match app.popup_focus {
                            PopupFocus::PathInput => PopupFocus::FileBrowser,
                            PopupFocus::FileBrowser => PopupFocus::PathInput,
                        };
                    }
                    KeyCode::Esc => app.toggle_popup(),
                    _ => match app.popup_focus {
                        PopupFocus::PathInput => match key.code {
                            KeyCode::Enter => {
                                let p = PathBuf::from(&app.popup_path_input);
                                if p.exists() && p.is_dir() {
                                    app.navigate_to(p);
                                    app.popup_focus = PopupFocus::FileBrowser;
                                }
                            }
                            KeyCode::Char(c) => {
                                app.popup_path_input
                                    .insert(app.popup_cursor_x, c);
                                app.popup_cursor_x += 1;
                            }
                            KeyCode::Backspace => {
                                if app.popup_cursor_x > 0 {
                                    app.popup_path_input
                                        .remove(app.popup_cursor_x - 1);
                                    app.popup_cursor_x -= 1;
                                }
                            }
                            KeyCode::Left => {
                                if app.popup_cursor_x > 0 {
                                    app.popup_cursor_x -= 1;
                                }
                            }
                            KeyCode::Right => {
                                if app.popup_cursor_x
                                    < app.popup_path_input.len()
                                {
                                    app.popup_cursor_x += 1;
                                }
                            }
                            _ => {}
                        },
                        PopupFocus::FileBrowser => match key.code {
                            KeyCode::Up => app.popup_list_up(),
                            KeyCode::Down => app.popup_list_down(),
                            KeyCode::Backspace => app.popup_list_back(),
                            KeyCode::Enter => {
                                if let Some(file_path) = app.popup_list_enter()
                                {
                                    app.toggle_popup();
                                    app.add_system_msg(format!(
                                        "Loading: {}",
                                        file_path
                                    ));
                                    match fs::read_to_string(&file_path) {
                                        Ok(src) => run_interpreter_step(
                                            interpreter,
                                            &mut app,
                                            &src,
                                        ),
                                        Err(e) => app.add_error(format!(
                                            "IO Error: {}",
                                            e
                                        )),
                                    }
                                }
                            }
                            _ => {}
                        },
                    },
                }
                continue;
            }

            match key.code {
                KeyCode::Char('l')
                    if key.modifiers.contains(KeyModifiers::CONTROL) =>
                {
                    app.toggle_popup();
                }

                KeyCode::Enter
                    if key.modifiers.contains(KeyModifiers::ALT)
                        || key.modifiers.contains(KeyModifiers::CONTROL) =>
                {
                    app.insert_newline();
                }
                KeyCode::Char('n')
                    if key.modifiers.contains(KeyModifiers::CONTROL) =>
                {
                    app.insert_newline();
                }
                KeyCode::Enter => {
                    let source = app.submit_input();
                    if source.trim() == "exit" {
                        break;
                    }
                    if !source.trim().is_empty() {
                        run_interpreter_step(interpreter, &mut app, &source);
                    }
                }

                KeyCode::Char(c) => app.insert_char(c),
                KeyCode::Backspace => app.delete_char(),
                KeyCode::Left => app.move_cursor_left(),
                KeyCode::Right => app.move_cursor_right(),
                KeyCode::Up => app.move_up(),
                KeyCode::Down => app.move_down(),
                KeyCode::PageUp => app.scroll = app.scroll.saturating_sub(5),
                KeyCode::PageDown => app.scroll = app.scroll.saturating_add(5),
                _ => {}
            }
        }
    }

    disable_raw_mode()?;
    execute!(terminal.backend_mut(), LeaveAlternateScreen)?;
    terminal.show_cursor()?;
    Ok(())
}

fn run_interpreter_step(
    interpreter: &mut Interpreter,
    app: &mut App,
    source: &str,
) {
    let saved_state = interpreter.state.clone();
    let saved_activations = interpreter.activations.clone();

    let capture = OutputCapture::new();

    interpreter.set_output(Box::new(capture.clone()));

    let result = execute_source(interpreter, source);

    interpreter.set_output(Box::new(io::stdout()));

    let output_text = capture.get_string();
    if !output_text.is_empty() {
        for line in output_text.lines() {
            app.add_message(Line::from(Span::styled(
                format!(" {}", line),
                Style::default().fg(Color::Yellow),
            )));
        }
    }

    match result {
        Ok(_) => {
            let stack_str = interpreter.stack_to_string();
            // Optional separator
            if !stack_str.is_empty() {
                app.add_message(Line::from(Span::styled(
                    "Stack:",
                    Style::default().add_modifier(Modifier::DIM),
                )));
            }
            for line in stack_str.lines() {
                app.add_message(Line::from(Span::styled(
                    line.to_string(),
                    Style::default().fg(Color::Cyan),
                )));
            }
        }
        Err(msg) => {
            app.add_error(format!("Error: {}", msg));
            interpreter.state = saved_state;
            interpreter.activations = saved_activations;
            interpreter.cache = None;
            let stack_str = interpreter.stack_to_string();
            for line in stack_str.lines() {
                app.add_message(Line::from(Span::styled(
                    line.to_string(),
                    Style::default().fg(Color::DarkGray),
                )));
            }
        }
    }
}

fn ui(f: &mut ratatui::Frame, app: &mut App) {
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Min(1),
            Constraint::Length(3 + app.input.len() as u16),
            Constraint::Length(1),
        ])
        .split(f.area());

    let messages_block =
        Block::default().style(Style::default().bg(Color::Reset));
    let msg_height = chunks[0].height as usize;
    let msgs_to_show = if app.messages.len() > msg_height {
        &app.messages[app.messages.len() - msg_height..]
    } else {
        &app.messages[..]
    };
    f.render_widget(
        Paragraph::new(msgs_to_show.to_vec())
            .block(messages_block)
            .wrap(Wrap { trim: false }),
        chunks[0],
    );

    let input_title = if app.history_index.is_some() {
        " Input (History) "
    } else {
        " Input "
    };
    let input_block = Block::default().borders(Borders::TOP).title(input_title);
    f.render_widget(
        Paragraph::new(app.input.join("\n")).block(input_block),
        chunks[1],
    );

    let status_bar = Paragraph::new(Line::from(vec![
        Span::styled(
            " [ Load File (Ctrl+L) ] ",
            Style::default().bg(Color::Blue).fg(Color::White),
        ),
        Span::raw(" "),
        Span::styled(
            " [ Exit (type 'exit') ] ",
            Style::default().bg(Color::DarkGray).fg(Color::White),
        ),
        Span::raw(" "),
        Span::styled(
            " [ Newline (Alt+Enter or Ctrl+N) ] ",
            Style::default().fg(Color::DarkGray),
        ),
    ]))
    .alignment(Alignment::Right);
    f.render_widget(status_bar, chunks[2]);

    if !app.show_file_popup {
        f.set_cursor_position((
            chunks[1].x + app.cursor.1 as u16,
            chunks[1].y + 1 + app.cursor.0 as u16,
        ));
    }

    if app.show_file_popup {
        let area = centered_rect(60, 50, f.area());
        f.render_widget(Clear, area);
        f.render_widget(
            Block::default()
                .title(" File Browser ")
                .borders(Borders::ALL)
                .bg(Color::Black),
            area,
        );

        let layout = Layout::default()
            .direction(Direction::Vertical)
            .constraints([Constraint::Length(3), Constraint::Min(0)].as_ref())
            .margin(1)
            .split(area);

        let path_style = if app.popup_focus == PopupFocus::PathInput {
            Style::default()
                .fg(Color::Yellow)
                .add_modifier(Modifier::BOLD)
        } else {
            Style::default().fg(Color::Gray)
        };

        let path_block = Block::default()
            .borders(Borders::ALL)
            .title(" Path (Tab to switch) ")
            .border_style(path_style);
        let path_p =
            Paragraph::new(app.popup_path_input.clone()).block(path_block);
        f.render_widget(path_p, layout[0]);

        let list_style = if app.popup_focus == PopupFocus::FileBrowser {
            Style::default().fg(Color::White)
        } else {
            Style::default().fg(Color::DarkGray)
        };

        let items: Vec<ListItem> = app
            .popup_entries
            .iter()
            .map(|(name, is_dir)| {
                let icon = if *is_dir { "📂 " } else { "📄 " };
                ListItem::new(format!("{}{}", icon, name))
            })
            .collect();

        let list = List::new(items)
            .block(
                Block::default()
                    .borders(Borders::ALL)
                    .title(" Files ")
                    .border_style(list_style),
            )
            .highlight_style(
                Style::default()
                    .bg(Color::Blue)
                    .fg(Color::White)
                    .add_modifier(Modifier::BOLD),
            )
            .highlight_symbol(">> ");

        f.render_stateful_widget(list, layout[1], &mut app.popup_list_state);

        if app.popup_focus == PopupFocus::PathInput {
            f.set_cursor_position((
                layout[0].x + 1 + app.popup_cursor_x as u16,
                layout[0].y + 1,
            ));
        }
    }
}

fn centered_rect(percent_x: u16, percent_y: u16, r: Rect) -> Rect {
    let popup_layout = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Percentage((100 - percent_y) / 2),
            Constraint::Percentage(percent_y),
            Constraint::Percentage((100 - percent_y) / 2),
        ])
        .split(r);

    Layout::default()
        .direction(Direction::Horizontal)
        .constraints([
            Constraint::Percentage((100 - percent_x) / 2),
            Constraint::Percentage(percent_x),
            Constraint::Percentage((100 - percent_x) / 2),
        ])
        .split(popup_layout[1])[1]
}

fn execute_source(
    interpreter: &mut Interpreter,
    source: &str,
) -> Result<(), String> {
    let parser_proxy = interpreter.vm.create_proxy();
    let mut parser = Box::new(Parser::new_object(
        &parser_proxy,
        &mut interpreter.heap,
        source.as_bytes(),
    ));
    let parser_obj = Tagged::new_ptr(parser.as_mut());
    let parse_msg = interpreter
        .vm
        .intern_string_message("parse", &mut interpreter.heap);
    let constants = vec![parser_obj.as_value(), parse_msg.as_value()];
    let instructions = vec![
        Instruction::new_data(OpCode::PushConstant, 0),
        Instruction::new_data(OpCode::Send, 1),
        Instruction::new(OpCode::Return),
    ];
    let dummy_body = interpreter.heap.allocate_array(&[]);
    let boot_code =
        interpreter
            .heap
            .allocate_code(&constants, &instructions, dummy_body);
    let boot_map = interpreter.heap.allocate_executable_map(boot_code, 0, 0);
    let boot_quotation = interpreter
        .heap
        .allocate_quotation(boot_map, unsafe { Handle::null() });
    interpreter.add_quotation(boot_quotation);
    if let ExecutionResult::Panic(msg) = interpreter.execute() {
        return Err(format!("Parser Panic: {}", msg));
    }
    let body_val = interpreter
        .state
        .pop()
        .ok_or("Parser did not return a value")?;
    if body_val == interpreter.vm.shared.specials.false_object.as_value() {
        return Err("Parsing failed".into());
    }
    let body_array = unsafe { body_val.as_handle_unchecked().cast::<Array>() };
    let code = BytecodeCompiler::compile(
        &interpreter.vm.shared,
        &mut interpreter.heap,
        body_array,
    );
    let code_map = interpreter.heap.allocate_executable_map(code, 0, 0);
    let quotation = interpreter
        .heap
        .allocate_quotation(code_map, unsafe { Handle::null() });
    interpreter.add_quotation(quotation);
    match interpreter.execute() {
        ExecutionResult::Normal => Ok(()),
        ExecutionResult::Panic(msg) => Err(format!("Panic: {}", msg)),
        res => Err(format!("Abnormal exit: {:?}", res)),
    }
}
