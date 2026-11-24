import GaugeFieldConstruction.SocotraC3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner
variable (P:BudgetPoint)
local notation "Sx"=> Support (More n)
local notation "LN"=> Orbit n → FC (Dwell n)
-- A root Ticket.
structure Factor3 (n:Side) where
    H: Hub n
    issue : Support (More n) → Orbit n → FC (Dwell n)
    raw : Orbit n → FC (Dwell n)
    pure : Bool
abbrev fadeN (F:Factor3 n):ℕ:= if F.pure then 0 else 2
lemma fade_sz(A:Factor3 n):fadeN A ≤2:=by unfold fadeN; split <;> norm_num -- tune notation
-- Halo elder S premises.E Cd moves.
structure LeaseQ (γ:Type)(n:Side) where
    H : γ→ Support (More n)
    X : γ→ Support (More n)
    issue : γ→ Support (More n)→ Copy n
    raw : γ→ Copy n
variable (V:RegLime I α n)(A:Factor3 n) (Q:LeaseQ γ n)
local notation "pack"=> Heart
variable (k:I)(σ:I→Seat n)
structure RegPay (P:BudgetPoint)(σ:I→Seat n)(r h:ℝ)(B:α→ℝ):Prop where
    wine(i)(D:Support (More n)): Medal P (V.S i) (V.S i∩D) (V.K i D) h (Bplain (V.V i).length (B i) r)
    qual(i)(D: Support (More n)): V.K i D≠0→ poke_F σ (V.S i) (V.V i).toFinset
    meet (i)(S D:Support (More n)) : V.S i ∩ S=V.S i∩ D → V.K i S=V.K i D
    turf(i)(T:Orbit n)(u:Ids n): V.K i ∅ (T.1,u)=V.K i ∅ T
structure Leased (P:BudgetPoint)(k:ℕ)(h:ℝ)(V:γ→ℝ) :Prop where
    later(i) : Q.H i⊆ Q.X i
    ready (i)(S D:Support (More n))(f:Q.X i⊆S)(u:Lattice.halo k D⊆ S): Medal P S D (Q.issue i D) h (V i)
    mint(i)(T:Orbit n)(t:Ids n): Q.issue i ∅ (T.1,t)= Q.issue i ∅ T
    qual(i)(U:Orbit n):Fock.Sector (camp (Q.H i)) false (Q.raw i U).val
    speak(i)(S D:Support (More n))(W:Orbit n)(w:Rue.FleetS P.threshold W.1) (f:Q.X i⊆S)(u:Lattice.halo k D⊆ S)(a:S∩ flags P.threshold W.1=D): Q.issue i D W=Q.raw i W
structure Act3 (P:BudgetPoint)(k:ℕ)(h p:ℝ):Prop where
    pays(S D:Support (More n))(g:A.H.val.2⊆ S)(v:Lattice.halo k D⊆ S):OpTheme S (A.issue D) false∧ Portμ (citrus P S D) 0 (A.issue D) h p P.order
    turf(T:Orbit n)(u:Ids n): A.issue ∅ (T.1,u)=A.issue ∅ T
    ready(S D: Support (More n))(W:Orbit n)(w:Rue.FleetS P.threshold W.1)(t:A.H.val.2⊆S)(p:Lattice.halo k D⊆ S)(v:S∩ flags P.threshold W.1=D): A.issue D W=A.raw W
    qual(U:Orbit n)(w:Rue.FleetS P.threshold U.1):Fock.Sector (camp A.H.val.2) false (A.raw U)
    -- per label.
    rank2(U): Leaf.rank2 (A.raw U)
    pure(U)(u:A.pure=true): Flour (camp A.H.val.2) (A.raw U)
variable (p d:ℕ)(hd:p+d ≤ fadeN A)(T:Heart A.H Q.H p) -- include all T even zero. use REAL supports.H.X containing all T genuines.L.Padding.
def ScopeΔ (Y:Hub n):= A.H.val.2⊆Y.val.2 ∧∀ j:Fin p,Q.X (T.val j)⊆ Y.val.2
variable (y:Hub n)(x:Heart y V.S d)
local notation "Πy" x:max=> Legist y V.S d x
abbrev βd (m:ℕ):= Fin m
abbrev Θu(x:Heart y V.S d):= x.val
def tags (x:Heart y V.S d):= (rosterF (univ:Finset (Fin d)) (fun i=> V.V (x.val i)))
def stamps (D:Support (More n)): α ⊕ γ→ Copy n:= Sum.elim (fun j=>V.K j D) (fun i:γ=>Q.issue i D)
def loomR(x:Heart y V.S d):List (α ⊕ γ):= (List.ofFn fun i=>Sum.inl (x.val i))++List.ofFn (fun i=>Sum.inr (T.val i))
def filmic (S:Support (More n)): Orbit n → FC (Dwell n) := discount p d • Coral (A.issue S) (stamps V Q S) (loomR V A Q p d T y x) -- steps
include hd
def peatE : Tuner I V.S:= ⟨y,d,(show d≤2 from (Nat.le_add_left ..).trans (hd.trans (fade_sz _))),fun x=>k:: tags V d y x,fun x _=>filmic V A Q p d T y x
    ⟩
omit hd
section
local notation "Zzp"=> Legist y V.S d x
variable {P:BudgetPoint}{r h a:ℝ}{g:α→ℝ}{l:γ→ℝ}{K:ℕ}
local notation "C" s:max=> stamps V Q s
local notation "W"=> loomR V A Q p d T y x
variable (u:RegPay V P σ r h g)(a0:Leased Q P K h l)(t:Act3 A P K h a) (q:ScopeΔ A Q p T y)
local notation "F" D:max=> filmic V A Q p d T y x D
theorem νt(x:Heart y V.S d)(i:Fin d):V.S (x.val i)⊆ (Πy x).val.2:= fun _ h=> mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,h⟩)
include u t a0 q
lemma μ_pay(X D:Support (More n))(b:(Legist y V.S d x).val.2 ⊆ X)(hp:Lattice.halo K D⊆ X)(hp':1≤h)(hc:0≤ g)(h1:0 ≤ l)(h2:0≤a)(hR:0< r): let z:= loomR V A Q p d T y x
 let Z(i:α⊕γ):= Sum.elim (fun j=> Bplain (V.V j).length (g j) r) l i
 (Portμ (citrus P X D) 0 (filmic V A Q p d T y x D) h (‖discount p d‖*((2:ℝ)^z.length*a*(z.map Z).prod)) P.order) ∧ OpTheme X (filmic V A Q p d T y x D) false:=by
 intro M L
 have hv(j:α⊕γ)(p:j∈ M): Medal P X D ((C D) j) h (L j):=by
    unfold M loomR at p; rcases List.mem_append.mp p with p|p <;> (rw [List.mem_ofFn] at p; obtain ⟨i,t,rfl⟩:=p) -- tune
    · let V':=V.S (x.val i); have hFF:V'⊆ X:= (νt V d y x i).trans b
      apply Medal.stretchB (u.wine (x.val i) D) hFF inter_subset_right _; intro j u'; obtain ⟨a,d⟩:= mem_sdiff.mp u'; exact mem_sdiff.mpr ⟨hFF a,fun g=>d (mem_inter.mpr ⟨a,g⟩)⟩
    exact a0.ready _ X D ((q.2 i).trans ((Finset.subset_union_left (s₁:=y.val.2)).trans b)) hp -- syntax
 have hs:=t.pays X D (q.1.trans (subset_union_left.trans b)) hp
 refine ⟨(Coralμ0 (A.issue D) (stamps V Q D) M P L X D hs.2 (fun i p=> colorIn _ _ _ _ (hv i p) hp') (fun i p=> (hv i p).wage (zero_le_one.trans hp')) h2).sMul _, opThemeScale _ (Coral0 (A.issue D) (stamps V Q D) M X hs.1 (fun i w=> (hv i w).toThemeR))⟩ -- args tune
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
