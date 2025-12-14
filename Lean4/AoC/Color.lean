module

@[expose] public section

namespace AoC.Color
/-- ANSI escape sequence for **red** foreground text. -/
def red     : String := "\x1B[001m\x1B[031m"
/-- ANSI escape sequence for **green** foreground text. -/
def green   : String := "\x1B[001m\x1B[032m"
/-- ANSI escape sequence for **blue** foreground text. -/
def blue    : String := "\x1B[001m\x1B[034m"
/-- ANSI escape sequence for **magenta** foreground text. -/
def magenta : String := "\x1B[001m\x1B[035m"
/-- ANSI escape sequence for **cyan** foreground text. -/
def cyan    : String := "\x1B[001m\x1B[036m"
/-- ANSI escape sequence to **reset** terminal styling (colors/attributes). -/
def reset   : String := "\x1B[000m"
/-- ANSI escape sequence to **revert** the previous line and clear it. -/
def revert  : String := "\x1B[1A\x1B[1G\x1B[1K"
/-- ANSI escape sequence for **reverse video** styling. -/
def reverse : String := "\x1B[001m\x1B[07m"

end AoC.Color
