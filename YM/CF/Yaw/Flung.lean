import YM.CF.Yaw.Yore
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Yaw
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
open Scion PetalP
open scoped Classical
variable {ι A n M:Type}[Fintype ι][DecidableEq ι][Fintype A][DecidableEq A][LinearOrder n][Fintype n][LinearOrder M][Fintype M]
local notation "K"=> LeanV M
local notation "vext"=> (twigExt : LeanV n ↪ Twig n)
local notation "veau"=> (twigCab : Oboe n ↪ Twig n)
variable {J:n→A}{D:LeanV M→A}{X:ι→ leaf A}{P:Finset ι}{a:Crowd A}
local notation "H₀"=> Crowd A
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}{k:ℕ}
variable {B:Raid (LeanV M)}{Q:Twig n→ Track (Crowd A) ℝ}{c:Twig n→ Track (Crowd A) (Raid (LeanV M))}{w:Twig n→Twig n→ Track (Crowd A) (Raid (LeanV M))}{U:PetalP (LeanV n)}{L:PetalP (Oboe n)} {b:Raid (LeanV M)}
lemma crankD {W Z: Track (Crowd A) (E→FC K)}{R F: Track H₀ (Raid K)}(p:deeds W k z a R)(g:deeds Z k z a F): deeds (crank W Z) k z a (Lay R F):=by
 intro i v; unfold crank Lay Stilo.coal; simp only [Finset.sum_apply]; apply Woody.sumV; intro j _; apply Woody.sumV; intro l _; simp_rw [Pi.single_apply]; split_ifs with c; · rw [c] at v; exact (p _ (le_sup_left.trans v)).pairP (g _ (le_sup_right.trans v))
 exact Woody.empty _ -- orientation
lemma hug_v (a:H₀)(b:Raid K)(t:0≤b): 0 ≤ (Pi.single a b:Track H₀ (Raid K)):=by intro i; rw [Pi.single_apply]; split_ifs; exact t; exact le_rfl
lemma heroV (a:H₀)(B b:Raid K):rateT B (Pi.single a b)=Pi.single a (joinV B b):=by funext i; simp_rw [rateT,Pi.single_apply]; split_ifs; rfl; simp [joinV]
structure PactW(z:E)(k:ℕ)(a:H₀)(U:PetalP (LeanV n))(L: PetalP (Oboe n))(F:E→ModeW J D X P)(c:Twig n→Track H₀ (Raid K))(w:Twig n→Twig n→ Track H₀ (Raid K))(b:Raid K):Prop where
 transit : TramS (fun y=>(F y).knots) z k a c w
 omega :Meant z k U put (fun y=>(F y).voice)
 eta : ∃ Y:E→FC n, Meant z k L bell Y ∧ ∀ i,i≤a→ ∀ᶠ y in 𝓝 z,(F y).rhythm i=Y y
 wear:∃ W:E→ FC (LeanV M), Woody k W z b ∧∀ i,i≤a→∀ᶠ y in 𝓝 z,(F y).diet i=W y
local notation "u'"=> Meant
include J D
lemma pay_g (C:P = P) (p: OfferS B Q c w)(f:0 ≤ U.led)(h:0≤ L.led)(u:0≤b) : ∃ R:Track H₀ (Raid K),0≤R ∧ rateT B R ≤ crank (crank (share U (Q∘vext)) (share L (Q∘veau))) (Pi.single (cluster X P) (joinV B b)) ∧ ∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](a:H₀)(z:E)(k:ℕ)(F:E→ModeW J D X P), PactW z k a U L F c w b → Woody k (fun x=> (vigor (F x) a).val) z (R a):=by
 obtain ⟨W,l,t,w'⟩:= pledgeL U L p f h; let η:=cluster X P; let L':Track H₀ (Raid K):= Pi.single η b; refine ⟨Lay W L',season W L' l (hug_v η _ u),(tFused p.peg l (hug_v η _ u)).trans ?_,fun E _ _ a z k F f=>?_⟩
 · unfold η; rw [heroV]; exact crank_r _ _ _ (by rw [← heroV (cluster X P) B b]; exact Turn_up p.peg (hug_v _ _ u)) t
 obtain ⟨Y,y,t⟩:=f.eta; obtain ⟨S,s,g⟩:= f.wear; let Z:Track H₀ (E→ FC K):= Pi.single η S; obtain ⟨W',d,v⟩:=w' E a z k _ _ _ f.transit f.omega y
 have he:deeds Z k z a L':= by intro i l; unfold Z L'; simp_rw [Pi.single_apply]; split_ifs; exact s; exact Woody.empty _
 let P':= crank W' Z; apply (crankD v he a le_rfl).germ; have hh(i:H₀)(t':i ≤ a):∀ᶠ y in 𝓝 z,(Scion.tempo (F y) i)=view i P' y:=by
    filter_upwards [g i t',t i t',d i t'] with y p h U; unfold Scion.tempo P' Z; rw [view_crank,singleV]; split_ifs with p'
    · change _=view i W' y * _; rw [h,U,p]
    exact (mul_zero _).symm -- tune
 filter_upwards [eventually_all.mpr (fun i:H₀=>eventually_all.mpr (hh i))] with y h
 symm; rw [vig_all]; refine proves (f:=reconL.symm _) (g:=fun i=>P' i y) ?_; intro i v; rw [recon,h i v]; simp [view,Finset.sum_apply]
lemma paysP (p: OfferS B Q c w)(f:0 ≤ U.led)(h:0≤ L.led)(u:0≤b) : ∃ R:Track H₀ (Raid K),0≤R ∧ rateT B R ≤ crank (crank (share U (Q∘vext)) (share L (Q∘veau))) (Pi.single (cluster X P) (joinV B b)) ∧∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](a:H₀)(z:E)(k:ℕ)(F:E→ ribbon M), (z∈tsupport F →∃ X_:E→ ModeW J D X P,PactW z k a U L X_ c w b ∧ ∀ᶠ y in 𝓝 z,F y=vigor (X_ y) a) → Woody k (fun x=> (F x).val) z (R a):=by
 obtain ⟨R,v,t,r⟩:=pay_g (J:=J) (D:=D) (X:=X) (P:=P) rfl p f h u; refine ⟨R,v,t,fun E _ _ a z k F g=>?_⟩; by_cases ht:z∈tsupport F
 · obtain ⟨X,h,t⟩:=g ht; exact (r E a z k X h).germ (t.mono fun i h=>Eq.symm (congrArg Subtype.val h))
 let X:=Woody.empty (n:=K) (k:=k) z; refine (show Woody k 0 z (R a) from ⟨X.own,fun i=> ⟨(X.haveP i).smooth,(X.haveP i).earned.trans (v a i)⟩⟩).germ ?_; filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with y s using Eq.symm (congrArg Subtype.val s)
end YM.CF.Yaw
