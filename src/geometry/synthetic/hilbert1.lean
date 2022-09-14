import  data.set tactic.interactive geometry.synthetic.hilbert_axioms
open classical
namespace Euclidean_plane
variables {point : Type} {line : Type }[Euclidean_plane point line]

local attribute [instance, priority 0] prop_decidable



theorem LinesOnePt {p p': point} {l1 l2 : line} (l1≠ l2): pointline p l1 →  pointline p l2 →  pointline p' l1 →  pointline p' l2 → p=p':=
begin
  intros hyp1 hyp2 hyp3 hyp4,
  apply by_contra,
  intros h,
  exact H( I1b p p' l1 l2 h hyp1 hyp3 hyp2 hyp4),

end

theorem afs (a b c  : point)  (l : line): pointline a l → pointline a l:=
begin
 tauto,
end
--def parallel (l1 l2 : line) : Prop := ∀ (a : point) pointline a l1 → ¬ pointline a l2


end Euclidean_plane
