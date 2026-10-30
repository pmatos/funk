func @"1"() {
^entry:
  ret @0
}

func @"a b"() {
^entry:
  ret @0
}

func @""() {
^entry:
  ret @0
}

func @"_ZN3foo$LT$E"() {
^entry:
  ret @0
}

func @"tab\tquote\"slash\\line\n"() {
^entry:
  ret @0
}

func @"\u{202e}hidden\u{85}\u{feff}\u{1}"() {
^entry:
  ret @0
}

func @"résumé"() {
^entry:
  ret @0
}

func @_start.v2() {
^entry:
  ret @0
}

locs {
  @0 = unknown
}
