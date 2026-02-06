use dot::escape_html;
use serde_derive::Serialize;
use std::borrow::Cow;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
pub enum Html {
    Text(Cow<'static, str>),
    Subscript(Cow<'static, str>),
    Seq(Vec<Html>),
    Font(&'static str, Box<Html>),
}

impl Html {
    pub(crate) fn space() -> Self {
        Html::Text(Cow::Borrowed(" "))
    }

    pub(crate) fn empty() -> Self {
        Html::Text(Cow::Borrowed(""))
    }

    pub(crate) fn text(&self) -> Cow<'static, str> {
        match self {
            Html::Text(text) | Html::Subscript(text) => text.clone(),
            Html::Seq(seq) => seq
                .iter()
                .map(Html::text)
                .collect::<Vec<_>>()
                .join("")
                .into(),
            Html::Font(_, html) => html.text(),
        }
    }
}

impl From<String> for Html {
    fn from(s: String) -> Self {
        Html::Text(s.into())
    }
}

impl From<&'static str> for Html {
    fn from(s: &'static str) -> Self {
        Html::Text(s.into())
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
                    .map(std::string::ToString::to_string)
                    .collect::<String>()
            ),
            Html::Font(face, html) => {
                write!(f, "<FONT FACE=\"{face}\">{html}</FONT>")
            }
        }
    }
}
