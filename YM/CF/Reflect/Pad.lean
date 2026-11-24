import YM.CF.Reflect.Carrier
import YM.CF.Reflect.Sides

/-! Three cone members which fit in order. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
attribute [local instance] opCStarAlgebra
section construction
variable {X E V : Type*} [TopologicalSpace X] [TopologicalSpace E] [CompactSpace E] [NormedAddCommGroup V] (h : X→E) (g : Continuous h)
def voiced (f : E→V) (e : Continuous f) : X→ᵇ V := (BoundedContinuousFunction.mkOfCompact (⟨f,e⟩:C(E,V))).compContinuous ⟨h,g⟩
lemma stackB (I : Type*) (D : Finset I) (F : I→X→ᵇ V) (x) : (∑ i∈D,F i) x=∑ i∈D,(F i) x := by
  classical
  induction D using Finset.induction_on with
  | empty=> simp
  | insert i D h ih=>rw [sum_insert h,sum_insert h,BoundedContinuousFunction.add_apply,ih]
end construction
variable {m B : Side} {X : Type*} [TopologicalSpace X] [Nonempty X]
variable (i : Axis) (x : Pack m B) (F : X→Pack m B) (p : Continuous F)
lemma zoneA (x : Pack m B) : Continuous (fun v : Pack m B × Pack m B=>tiedK m B i x v.1 v.2) := by
  let f := fun v:Pack m B× Pack m B=> (x,v); exact (show Continuous (quill m B i) from tiedC i).comp (show Continuous f from continuous_const.prodMk continuous_id)
include p
lemma accomplish (c : Foot m B) (t : ℝ) (h : 0 ≤ t) : ∃ W : CSeat X (Xmind m B), W∈Cloud (finger m B i) (colony m B i) X ∧ ∀ u:X× X,
    W u=quant (n:= Model (CSide m B)) (grow (wiel m B (axisCut m B i c) (tiedK m B i x (F u.1) (F u.2)).1) t) := by
  let V := Skin m B
  let L := Ledge m B i; let S := colony m B i; let U := finger m B i; let s := tiedK m B i x; let d := axisCut m B i c
  let z (u:X) : Skin m B := (s (F u) (F u)).1
  have hg : Continuous z := continuous_fst.comp ((zoneA i x).comp (p.prodMk p))
  let A := enter m B i; let B' := exitK m B i
  let D := dg (n:=Xmind m B)
  let Y := fun v:Skin m B=>D (L*wiel m B d v * L)
  have hy : Continuous Y := (show Continuous D from dg_cont).comp ((continuous_const.mul (wiel_cont d)).mul continuous_const)
  let M0 : CBox X (Xmind m B) := voiced z hg Y hy
  have H₀ : Hut S false M0 := fun x=> abs_dg ..
  let f := t • M0
  have hf : Hut S false f := fun u' => by
    change Sector S false (t • M0 u'); rw [←show (t:ℂ) • M0 u'=t • M0 u' by ext i j; simp [Complex.real_smul]]; exact (H₀ u').scale _
  let C := CBox X (Xmind m B)
  -- channel array: separate for each of two boundaries
  have hb (A:Skin m B→Op (Xmind m B)) (e : Continuous A) (h : ∀ u,L*A u=A u) : ∃ O:CSeat X (Xmind m B), Faced U S O ∧ ∀ u:X×X,
      O u=∑ j:Xmind m B, (chord true • (theta U (remove (acts (A (z u.2)) (basisKet j)))*remove (acts (A (z u.1)) (basisKet j)))+
                        chord true • (theta U (create (acts (A (z u.2)) (basisKet j)))*create (acts (A (z u.1)) (basisKet j)))) := by
    let c := Xmind m B
    let f := fun j v=> create (n:=c) (acts (A v) (basisKet j)); let g := fun j v=> star (f j v)
    have he j : Continuous (f j) := create_cont.comp ((acts_cont.comp e).clm_apply continuous_const)
    let V j := voiced z hg (f j) (he j); let L' j := voiced z hg (g j) (he j|>.star)
    have hv j : Hut S true (V j) := fun i=> Sector.makeP _ (by change acts L _=_; rw [←act_mul,h])
    have ht j : Hut S true (L' j) := fun i=> (hv j i).contr
    let O := ∑ j:Xmind m B,(tile U true (L' j)+tile U true (V j)); refine ⟨O,Faced.sumX _ _ (fun j _=> (Faced.square _ _ (ht j)).plus (Faced.square _ _ (hv j))),?_⟩
    intro u; unfold O; rw [stackB]; apply sum_congr rfl; intro j _; rw [BoundedContinuousFunction.add_apply]; rfl
  obtain ⟨O,g,hO⟩ := hb A (enter_cont i) (enter_pos i)
  obtain ⟨T,u,hT⟩ := hb B' (exit_cont i) (exit_pos i)
  let Y := opposite U f+direct f+t • (O+T)
  refine ⟨exp Y, attendsCone f _ hf ((g.plus u).raise t h) (movedCol m B i),?_⟩
  intro u; rw [eval_exp, ferment (n:=Xmind m B) (show IsSelfAdjoint _ from self_wiel ..)]
  congr 1
  change theta U (t • D (L*wiel m B d (z u.2)*L))+t • D (L*wiel m B d (z u.1)*L)+t • (O u+T u)=_
  rw [theta_rsmul,←smul_add,←smul_add,waking i x c (F u.1) (F u.2),hO,hT]
omit p in
lemma absolute (n : Type*) [LinearOrder n] [Fintype n] (S : Finset n) (k : ℝ) : ∃ M:ℝ, ∀ C : Op n, ‖C‖ ≤ k → ‖seedR S C‖≤M := by
  obtain ⟨b,h⟩ := ((isCompact_closedBall (0:Op n) k).image (continuous_seed S |>.norm)).bddAbove
  exact ⟨b,fun c g => h (show ‖seedR S c‖ ∈ _ from ⟨c,by simpa using g,rfl⟩)⟩ -- remove p includes
omit p -- tune move
lemma anterior {e : ℝ} (b : Room B e) (p : Continuous F) (K : ∀ y z : X,tiedK m B i x (F y) (F z) ∈ payer m B e) : ∃ A:CSeat X (Xmind m B), A∈Cloud (finger m B i) (colony m B i) X ∧ ∀ u:X×X,
   acts (A u) (linearB (CSide m B))=pairWave (n:= Model (CSide m B)) (pair m B (tiedK m B i x (F u.1) (F u.2)).1 (tiedK m B i x (F u.1) (F u.2)).2) := by
  let U := finger m B i; let s := tiedK m B i x; let S := Ledge m B i; let g := fun u=> s (F u) (F u); let Y u:= Slater m B i (g u)
  have hp : Continuous g := (zoneA i x).comp (p.prodMk p)
  have hx : Continuous (fun u=> pair m B (g u).1 (g u).2) := (pair_cont b).comp_continuous hp (fun i=>K i i) -- tune
  have he : Continuous Y := (continuous_seed _).comp ((continuous_const.mul hx).mul continuous_const)
  obtain ⟨c,L⟩ := absolute (Xmind m B) (upperP (CSide m B)) 1
  have hv u : ‖Y u‖≤c := by
    apply L; have h : ‖S‖≤1 := (cutM_idp _).norm_le _
    let A := pair m B (g u).1 (g u).2
    have hy : Valid _ A := kappa (0:Phase.Part m B) b (K u u).1 (K u u).2
    apply (norm_mul_le (S*A) S).trans
    have ht := norm_mul_le S A; rw [CStarRing.norm_of_mem_unitary hy.1,mul_one] at ht
    exact (mul_le_mul (ht.trans h) h (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
  let f : CBox X (Xmind m B) := BoundedContinuousFunction.ofNormedAddCommGroup Y he c hv
  let P := opposite U f+direct f+0; refine ⟨exp P,attendsCone f 0 (fun u=>initial_sector i (g u)) Faced.zero (movedCol m B i),?_⟩
  intro u; let w := s (F u.1) (F u.2); let z := pair m B w.1 w.2
  have hk (v w:Pack m B) (h : NorthOf m B i v w) : Slater m B i v=Slater m B i w := congrArg (seedR (upperP (CSide m B))) (opens_pair i h)
  have hl : P u= theta U (Slater m B i (g u.2))+Slater m B i (g u.1) := by unfold P; rw [add_zero]; rfl
  rw [eval_exp, harvest_x (c:=0) b (K u.1 u.2), hl,initial_think i b (K u.1 u.2)]; simp_rw [sew i, hk _ _ (strum i x (F u.1) (F u.2) (F u.1)), hk _ _ (strum i x (F u.2) (F u.1) (F u.2))] -- tune
  rw [add_comm (theta U _)]
end YM.CF.RP
