abbrev Ledger := List (Nat × Rat)

namespace Ledger

def held (l : Ledger) : Rat := 1 - (l.map Prod.snd).sum
