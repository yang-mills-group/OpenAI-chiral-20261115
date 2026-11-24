import YM.CF.Scion.Facet
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]

set_option maxHeartbeats 500000
open Pec Proa Hest Hive Spire Skye Levier Cascade Kennel

open Cour Acorn Atala Reef MeasureTheory Jet
variable {N B:Side}(X Y:Support (Domain N B))(D e:ℝ)(J:Pride (mid N B))(u: ℕ)
abbrev turP (i:Bool):Castle N B e X→ CapX N B e:=fun v=>⟨v.val i,v.property.1 i⟩
lemma turnCop(i:Bool): Cop (newX (Spire.soar N B e) (aether u D e N B) u) (landX u D X e) (turP X e i):=by
 constructor
 · rfl
 · rfl
 · exact (((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
 · intro S x y v; exact v i
 intro A _ _ _ V v p t x h; exact t _ h i
lemma offCop (h:Disjoint X Y)(v:Castle N B e X): (newX (Spire.soar N B e) (aether u D e N B) u).moves Y (turP X e false v) (turP X e true v):=by
 apply Lattice.agrees_mono v.property.2; exact fun i p=>mem_compl.mpr (fun t=>Finset.disjoint_left.mp h t p)
-- absolute wind fits. unify pay via Ink ledger. exp * mass support
abbrev Tints (N B:Side)(e:ℝ):=∀ X:Seal (Site (Domain N B)), Seal (Site (Domain N B))→ Castle N B e X→ℂ -- autoimplicit param types todo
def hoopI(x:Castle N B e X):= Complex.exp (pigment J (x.val false)-pigment J (x.val true))
structure Dyes (D e:ℝ)(J:Pride (mid N B))(u:ℕ) (K:Tints N B e)(a h:ℝ) : Prop where
 arch (S:Seal (Site (Domain N B)))(p:Grove (terr _) S):∃ C:Seal (Site (Domain N B))→ℝ,(∀ i, Acorn.Pro (landX u D S e) i (K S i) (C i) ∧ (C i≠0 → S⊆ i)) ∧ (∑ i,Acorn.cost a S i*C i) ≤ Real.exp (h*S.card) ∧ ∀ x, hoopI S e J x=∑ i,K S i x
lemma cropsI (n:ℕ){v t:ℝ}(h:0<v)(hk:1 ≤ D)(hp:0<t) : ∃ a b:ℝ,0<a∧0≤b∧∀ m B:Side,∀ e:ℝ,∀ R:Pride (mid m B),Lac R v t→ ∃ K:Tints m B e,Dyes D e R n K a b:=by
 classical
 obtain ⟨C,p,H⟩:=lumpP v h D hk n t hp.le; have hu:=Acorn.one_w n; let L:= Acorn.worth n * (2*C); have he:0<v/18:=by positivity
 refine ⟨_,L,he,(by unfold L; have he:0≤ Acorn.worth n:=zero_le_one.trans hu; positivity),fun m B e R g=>?_⟩; obtain ⟨F,K,x,l,v0⟩:= (H m B R g.pay e)
 have hr(S:Broc.Table m B) (w:Grove (terr _) S):Cash (landX n D S e) S (v/18) (hoopI S e R) (Real.exp (L*S.card)):=by
    have hh:S.Nonempty:=by cases w <;> simp
    let f(x:CapX m B e):= pigment R x.val; have hv:= Cash.off (A:=f) S hh (show Grove (landX n D S e).frame S from w) (turnCop S D e n false) (turnCop S D e n true) (fun i p t=> offCop S i D e n p t) F K (fun i=> ⟨(x i).pos,(x i).travel,(x i).cont,(x i).sumline,(x i).reads,(x i).plot⟩) he.le l v0
    unfold L; rw [show Acorn.worth n*(2*C)*(S.card:ℝ)=Acorn.worth n*((S.card:ℝ)*(2*C)) by ring]; exact hv.embark he.le hh w
 choose V Y h using (fun (S:{S:Broc.Table m B//Grove (terr _) S})=>hr S.val S.property); let M(S:Broc.Table m B): Seal (Site (Domain m B))→ Castle m B e S→ℂ:= if p:Grove (terr _) S then V ⟨S,p⟩ else 0
 refine ⟨M,⟨fun S p=>?_⟩⟩; dsimp only [M]; rw [dif_pos p]; exact ⟨_,h ⟨S,p⟩⟩
end YM.CF.Scion
