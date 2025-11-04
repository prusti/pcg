use dot::escape_html;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Html {
    Text(String),
    Subscript(String),
    Seq(Vec<Html>),
    Font(&'static str, Box<Html>),
}

impl Html {
    pub(crate) fn text(&self) -> String {
        match self {
            Html::Text(text) => text.clone(),
            Html::Subscript(text) => text.clone(),
            Html::Seq(seq) => seq.iter().map(|h| h.text()).collect::<Vec<_>>().join(""),
            Html::Font(_, html) => html.text(),
        }
    }
}

impl From<String> for Html {
    fn from(s: String) -> Self {
        Html::Text(s)
    }
}

impl<'a> From<&'a str> for Html {
    fn from(s: &'a str) -> Self {
        Html::Text(s.to_string())
    }
}

impl std::fmt::Display for Html {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Html::Text(text) => write!(f, "{}", escape_html(text)),
            Html::Subscript(text) => write!(f, "<SUB>{text}</SUB>"),
            Html::Seq(seq) => write!(
                f,
                "{}",
                seq.iter()
                    .map(|h| h.to_string())
                    .collect::<Vec<_>>()
                    .join("")
            ),
            Html::Font(face, html) => {
                write!(f, "<FONT FACE=\"{face}\">{html}</FONT>")
            }
        }
    }
}
