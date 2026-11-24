import YM.CF.BProof.Gates.Flags

/- receipts shorthand. core labels sign membership remains actual field from Mark U.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gates.Stage.Setup
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing Micro
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}(P:Entice S L a d y){s:Side}(Y:S.Setup L a s d y)
variable (T:PathData G)(θ:ℝ)(x:Pawn Y.yard)
abbrev soil := (pulse P Y).X
abbrev camp := Y.yard
abbrev slot := Y.hall
abbrev color := Pawn.rent Y.hall x y T θ (soil P Y)
abbrev area := Pawn.put Y.hall x y T θ (soil P Y)
abbrev Along : Prop:= Pawn.Rich Y.yard Y.hall y T θ (soil P Y) S.κ x
abbrev F' := Pawn.issue x y T θ (soil P Y)
abbrev certified := Y.yard.accepted y Y.hall (F' P Y T θ x) x.mood
def bad := (Model.raw y Y.yard x.sev x.gauss).image (House.hide Y.yard Y.g)
lemma yard_climb (h:certified P Y T θ x): Y.yard.Climbed y Y.hall (F' P Y T θ x) (color P Y T θ x):= Y.yard.climbed y Y.hall _ _ h
lemma account_f (h:certified P Y T θ x): Y.yard.Climbed y Y.hall (area P Y T θ x) (color P Y T θ x):=by
 let Z:=color P Y T θ x; let U:=area P Y T θ x; intro i hi; unfold lifts; intro b; rw [Y.yard.sweeps_eq i U (W:= F' P Y T θ x) (Y.yard.mix_field ..) hi b]; exact yard_climb P Y T θ x h i hi b -- tune names conflict area defs
include P
lemma seen : Seen Y.hall.K y:=P.dull.seen
lemma flags (hT:T.Bounds c w R v) (u:θ∈Set.Icc (1/2) 2)(o:Along P Y T θ x)(t:Site s)
    (h:t∈RG.flags (thresh y) (area P Y T θ x)) : ∃ j∈x.sev, Y.yard.Gap j.1 (time t)∧ Grid.dist (BProof.space t) j.2 ≤4:=by
 let p:= P.dull; let C':=area P Y T θ x
 obtain ⟨h₀,h₁,h₂,h₃⟩:= Y.proceeds P T θ x o
 have he:= Release.holds S.K S.P Y.yard T θ S.κ y (soil P Y) (room P Y) hT u ((pulse P Y).bought S.K S.P c S.M R Y.yard y S.κ) x.sev x.gauss (area P Y T θ x) x.gap (Y.yard.mix_field ..) h₁ h₀
 obtain ⟨i,w,p,a,v⟩:= markFor P Y C' h₃ (Y.account_f P T θ x o.2.2.1) t h he; refine ⟨(i,p),?_ ,w,(Grid.dist_symm ..).trans_le v⟩; rw [← Release.cash Y.yard T θ S.κ y (soil P Y) x.sev x.gauss C' x.gap (Y.yard.mix_field ..) h₁]; exact a
include P
lemma θ_t (β:ℝ)(h:y≤2*β)(v:β≤2*y): (β*CF.BProof.g y^2:ℝ) ∈ Set.Icc (1/2) 2:=by
 have hx:0<y:=zero_lt_two.trans_le P.dull.threshY; rw [show CF.BProof.g y^2=y⁻¹ by nth_rw 2 [← coinY hx]; rw [coin_pow, coin_inv]; ring_nf]; field_simp; change _≤ β / y ∧ β/y≤2 -- tune
 exact ⟨(le_div_iff₀ hx).2 (by linarith), (div_le_iff₀ hx).2 v⟩
end YM.CF.BProof.Gates.Stage.Setup
