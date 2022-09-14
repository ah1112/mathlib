

class Euclidean_plane (point : Type) (line : Type):=
-- Equidistance of 4 Points

(pointline : point → line → Prop)
--pointline P L means P is on L
(eqd : point → point → point → point → Prop)

-- Between A B C means B is on the line segment AC
(B : point → point → point → Prop)
[dec_B : ∀ a b c, decidable (B a b c)]

(P1 {} : point) (P2 {} : point) (P3 {} : point)

(I1a : ∀ (a b : point), a≠b → ∃ (l: line) , pointline a l ∧ pointline b l)
(I1b : ∀ (a b : point), ∀ (l l': line), a≠b →  pointline a l →  pointline b l →  pointline a l' →  pointline b l'  →l=l')
(I2 : ∀ l : line, ∃ (X:point×point), pointline X.1 l ∧ pointline X.2 l ∧ X.1≠ X.2)
(I3 : ¬ ∃ l : line , pointline P1 l ∧ pointline P2 l ∧ pointline P3 l)




-- Existence of three points for two_dim
