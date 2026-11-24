import YM.SU5.FiniteGaugeData.Tower.Atlas
import YM.SU5.FiniteGaugeData.Tower.Reflect
import YM.SU5.FiniteGaugeData.Tower.Schedule
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)

/-!
# Finite (charged) resolution diagram

On the actual Course, using just the terrain parameter as actual level-size
identification, including for varying arguments on one period or support; don't
infer cross-level identification just by this cast. `block` will supply that
identification for *marks at this stage* explicitly, with the same history:
original Sharp Ratio preserving via stove+advance.
-/
open Fock

section shipments
variable {c d:Side}(h:c=d)
def ship (i:Mark c):Mark d:= h ▸ i
def migration (x:Fields c):Fields d:=h ▸ x
def fold_op (x:FC (Single c)):FC (Single d):=h▸ x
lemma unification (i:Mark c)(x:Fields d): ship h i x=fold_op h (i (migration h.symm x)):=by subst c; rfl
lemma reverse (i:Mark d): ship h (ship h.symm i)=i:=by subst c; rfl
lemma ship_arith (F G:Mark c)(z:ℂ): ship h (F+G)=ship h F+ship h G ∧ ship h (F*G)=ship h F*ship h G ∧ ship h (z•F)=z•ship h F ∧ ship h 1=1 ∧ ∀ a t, ship h (reflMark a t F)= reflMark a t (ship h F):=by subst c; simp [ship]
lemma ship_box (S:Finset Cover){F:Mark c}{b:Bool}(p:AtSupport b (Satin.region S c) F): AtSupport b (Satin.region S d) (ship h F):=by subst c; exact p
end shipments

section chemistry
-- κ = actual Course stage, n = cutoff index, s native observing level.
variable (S:Finset Cover)(κ n:ℕ)
abbrev legalAt: Prop := (Y.voyage κ).kick≤ n ∧ s< Y.uv n
local notation "Z₀"=> Y.voyage κ
local notation "Xs"=> ((Z₀).X (Y.uv n)).gram
local notation "Qs"=> ((Z₀).X (Y.uv n)).wave
local notation "R₀"=> (Z₀).CapeT
local notation "A₀"=> steps Λ.V (Y.ir κ) Λ.block (Y.uv n)
local notation "b₀"=> Λ.R.L
local notation "D₀"=> aliasLaw Λ
local notation "u₀"=> distanceLaw l
local notation "g₀" t=> apt (Y.ir κ) Λ.block (b₀) t
local notation "θ" => Chi.canonical
local notation "μ" t => momentm Y κ t
local notation "c" t => (K).c (μ t)
local notation "d" t => side Y κ t
local notation "e" t=>terrain Y H (Y.ir κ) t
-- position all Fock operators in the canonical η and AP conventions precisely at native level
noncomputable def distribute (f:Family (tent Y H)) : Mark (side Y κ s):= ship (e s) (f (momentm Y κ s))
lemma distribute_arith (F G:Family (tent Y H))(z:ℂ): let l:=distribute Y H s κ
 l (F+G)=l F+l G ∧ l (F*G)=l F*l G ∧ l (z • F)=z • l F∧ l 1=1 ∧∀ a t, l (mirror (tent Y H) a t F)=reflMark a t (l F):=by
 intro l; exact ship_arith (e s) (F (μ s)) (G (μ s)) z
lemma notation_note (u:Chorus)(f:PairsC→ℂ): distribute Y H s κ (note (tent Y H) f u)= knot (side Y κ s) u f:=by
 unfold distribute; rw [kiosk]; apply same_knot
where same_knot{c₀ d₀:Side}(h:c₀=d₀)(u:Chorus)(f:PairsC→ℂ): ship h (knot c₀ u f)=knot d₀ u f:=by subst c₀; rfl
lemma stationed {F:Family (tent Y H)} (p:InTest K true S false F):AtSupport false (Satin.region S (side Y κ s)) (distribute Y H s κ F):=ship_box (e s) S (p.support _)
lemma stationary_ext {F G:Family (tent Y H)} (p:Hosp S ((K).c (μ s)))(x:InTest K true S false F)(y:InTest K true S false G)(z: distribute Y H s κ F=distribute Y H s κ G):F=G:=by
 refine box_ext (tent Y H) S x y p ?_
 exact charge_id (e s) z
where charge_id{c₀ d₀:Side}(h:c₀=d₀){a b:Mark c₀}(z:ship h a=ship h b):a=b:=by subst c₀; exact z

noncomputable def aboveD (F:Family (tent Y H)): Mark (side Y κ (s+1)):=
 nextMark (j:=Λ.K.j) (ho:=Λ.R.odd_side) (Xs) (R₀) θ Λ.J.d (Qs) (A₀) s (distribute Y H s κ F)
local notation "T" F=> aboveD Y H s κ n F
abbrev wingspan(Λ:Preparation)(l:ℕ)(S:Finset Cover) :=
 Satin.liner (S.image (fun a=> Λ.R.L.val • a)) (Λ.R.L.val*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J)
lemma wingspan_mono{Λ:Preparation}{l:ℕ}:Monotone (wingspan Λ l):=by
 rintro S U p x v; obtain ⟨i,h,g⟩:= Finset.mem_biUnion.mp v; exact Finset.mem_biUnion.mpr ⟨i,Finset.image_subset_image p h,g⟩
local notation "S₊" U:max=> wingspan Λ l U
variable (p:legalAt Y s κ n)
include p
lemma upper {F:Family (tent Y H)}(h:InTest K true S false F): AtSupport false (Satin.region (S₊ S) (d (s+1))) (T F):=by
 let k:= (fullness Y κ n p.1).cap_grant
 obtain ⟨U⟩:= k.grant s p.2; obtain ⟨y,b,h₀,F0,s'⟩:= U.cap
 have v:= surround (g₀ s) ((A₀) s) Λ.K.j ((Qs) s).val ((Xs) (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d ((Xs) (s+1)).beta ((R₀) s) (show Stencil.LaurentRadius Λ.K.j (b₀) D₀ from Journey.legal Λ) F0.bill (k.branch s p.2) U.legal.1 U.legal.2 (distribute Y H s κ F) (stationed Y H s S κ h) (tissue Y κ s) (k.aligned s p.2)
 have eq:((A₀) s).patch.J=Λ.R.J:=k.radius s p.2; rw [eq] at v
 exact v.mono (next_contains S _ (side Y κ s) (apt ..))
lemma promise {F:Family (tent Y H)}(h:InTest K true S false F):Journey.compass Y κ n (s+1) (T F)=sharp Y H s κ n F:=by
 let k:= (fullness Y κ n p.1).cap_grant; have hX:= single_num Λ.U (Xs) (R₀) θ Λ.J.d (Y.uv n) (Qs) (A₀) (Journey.legal Λ) k ((stationed Y H s S κ h).mono (Finset.subset_univ _)) p.2
 change Journey.compass Y κ n (s+1) (aboveD Y H s κ n F)= Journey.compass Y κ n s (distribute Y H s κ F)
 unfold Journey.compass aboveD; rw [hX,((Y.voyage κ).X (Y.uv n)).balance (s+1) p.2,← ((Y.voyage κ).X (Y.uv n)).balance s p.2.le]

omit p
noncomputable def distribute_back (S:Finset Cover)(f: Mark (side Y κ s)) : Family (tent Y H) := if v:Tivoli S ((K).c (μ s)) then extendAtlas S (tent Y H) (momentm Y κ s) v (ship (e s).symm f) else 0
lemma stationed_back (f:Mark (side Y κ s))(h:AtSupport false (Satin.region S (side Y κ s)) f): InTest K true S false (distribute_back Y H s κ S f):=by
 unfold distribute_back; split
 next v=> exact dictionary _ _ _ _ _ (ship_box (e s).symm S h)
 next=> exact InTest.zero
lemma authorized_back (f:Mark (side Y κ s))(h:AtSupport false (Satin.region S (side Y κ s)) f)(v:Tivoli S ((K).c (μ s))): distribute Y H s κ (distribute_back Y H s κ S f)=f:=by
 unfold distribute distribute_back; rw [dif_pos v,Tower.native S K (μ s) v _ (ship_box (e s).symm S h),reverse]

-- main finite-stage definition returns zero declaration if the step or lift
-- not bought. (off-stage prices will use zero for convergence purposes only.)
noncomputable def block (S:Finset Cover)(F:Family (tent Y H)):Family (tent Y H) := if legalAt Y s κ n∧ InTest K true S false F then distribute_back Y H (s+1) κ (S₊ S) (T F) else 0
lemma booked (S:Finset Cover)(F:Family (tent Y H)): InTest K true (S₊ S) false (block Y H s κ n S F):=by
 unfold block; split
 next v=> exact stationed_back Y H _ _ _ _ (upper Y H s S κ n v.1 v.2) -- order
 next=> exact InTest.zero

include p
lemma reserved {F:Family (tent Y H)}(x:InTest K true S false F)(v:Tivoli (S₊ S) ((K).c (μ (s+1)))): distribute Y H (s+1) κ (block Y H s κ n S F)=aboveD Y H s κ n F:= by
 unfold block; rw [if_pos ⟨p,x⟩]; exact authorized_back Y H _ _ _ _ (upper Y H _ S _ _ p x) v
lemma upper_coupling {F:Family (tent Y H)}(x:InTest K true S false F)(v:Tivoli (S₊ S) ((K).c (μ (s+1)))): sharp Y H (s+1) κ n (block Y H s κ n S F)=sharp Y H s κ n F :=by
 change Journey.compass Y κ n (s+1) (distribute Y H (s+1) κ (block Y H s κ n S F)) = _
 rw [reserved Y H s S κ n p x v,promise Y H s S κ n p x]

lemma upper_overlap {F:Family (tent Y H)}(x:InTest K true S false F){U:Finset Cover}(u:S⊆U)(v:Tivoli (S₊ U) ((K).c (μ (s+1)))):
 block Y H s κ n U F=block Y H s κ n S F:=by
 have ht:Satin.tips (S₊ S) ⊆ Satin.tips (S₊ U):=by
    intro a h; rcases Finset.mem_union.mp h with h|h
    · exact Satin.tips_here _ (wingspan_mono u h)
    obtain ⟨i,t,sH⟩:= Finset.mem_biUnion.mp h
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,wingspan_mono u t,sH⟩)
 exact stationary_ext Y H _ _ _ (v.hosp) (booked Y H ..) ((booked Y H s κ n S F).mono (wingspan_mono u)) (by rw [reserved Y H s U κ n p (x.mono u) v,reserved Y H s S κ n p x ⟨⟨v.tips_x.seat_.mono ht⟩⟩])
end chemistry
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.upper_overlap
#print axioms YM.CF.Buffered.Afterglow.Tower.upper_coupling
