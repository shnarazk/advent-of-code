module 

@[expose] public section

namespace AoC.Color

def red     : String := "\x1B[001m\x1B[031m"
def green   : String := "\x1B[001m\x1B[032m"
def blue    : String := "\x1B[001m\x1B[034m"
def magenta : String := "\x1B[001m\x1B[035m"
def cyan    : String := "\x1B[001m\x1B[036m"
def reset   : String := "\x1B[000m"
def revert  : String := "\x1B[1A\x1B[1G\x1B[1K"
def reverse : String := "\x1B[001m\x1B[07m"

end AoC.Color
