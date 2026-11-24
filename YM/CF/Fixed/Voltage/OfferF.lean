import YM.CF.Fixed.Voltage.PermitF
/-! Prices full addresses retain every flag. Strong only at fixed volume: appears in tiny reorg not at varying positions. -/
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.CF.Fixed.Voltage
open Function NormedSpace Filter Metric Finset Lattice Wilson SU Scree Skye Fock Lat Cube MeasureTheory Vow RG Rue Spire
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {n:Side}{x a b h w:ℝ}(P:BudgetPoint)(D:Support (More n)) {Q:Sweep n→Prop}
local notation "N"=> More n
local notation "A"=> deck_F P D
variable {F G:Copy n}
structure Metered (F:Copy n)(w C:ℝ):Prop where
 meter: Medal P univ D (hours P D F) w C
namespace Metered
variable {P D} (H:Metered P D F w a) (J: Metered P D G w b)
include H in
lemma mono (l:a ≤ h): Metered P D F w h:= ⟨H.meter.big l⟩
include H in
lemma related(u:∀ V:Orbit n, V.1∈ deck_F P D→ F V=G V): Metered P D G w a:=⟨(show hours P D F=hours P D G from (funext (fun i=> by
 by_cases h:i.1∈ deck_F P D
 · rw [unveil_F _ _ _ _ h,unveil_F _ _ _ _ h,u i h]
 rw [shut_F _ _ _ _ h,shut_F _ _ _ _ h]))) ▸ H.meter⟩
include H in
lemma holds(he:0≤w):0≤a:= H.meter.wage he
lemma of_cast(l:Medal P univ D F w a): Metered P D F w a:=⟨deck_keep _ _ _ _ l⟩
include H J in
lemma link:Metered P D (F+G) w (a+b):=by 
  refine ⟨?_⟩
  have he:= H.meter.plus J.meter; change Medal P univ D (Set.indicator _ (F+G)) w _; rw [Set.indicator_add']; exact he
include H in
lemma stow(z:ℝ):Metered P D (z • F) w (|z| * a):=by
  refine ⟨?_⟩; have he:= H.meter.rum z; have hx(i:Orbit n): hours P D (z • F) i=z • hours P D F i:=by unfold hours; by_cases h:i.1∈ deck_F P D; rw [Set.indicator_of_mem (show i∈_ from h),Set.indicator_of_mem (show i∈_ from h)]; rfl; rw [Set.indicator_of_notMem (show i∉_ from h),Set.indicator_of_notMem (show i∉_ from h),smul_zero]
  rw [show hours P D (z • F)=z • hours P D F from funext hx]; exact he
include H in
lemma tint:Metered P D (-F) w a:=by simpa using H.stow (-1)
lemma diff (H:Metered P D F w a)(J:Metered P D G w b):Metered P D (F-G) w (a+b):=by rw [sub_eq_add_neg]; exact H.link J.tint
include H J in
lemma cross(v:0≤w):Metered P D (F*G) w (a*b):=by
  have he(i:Orbit n): hours P D (F*G) i = (hours P D F * hours P D G) i:= by by_cases h:i.1∈ deck_F P D; simp [Pi.mul_apply,unveil_F _ _ _ i h]; simp [Pi.mul_apply,shut_F _ _ _ i h]
  exact ⟨(funext he) ▸ (H.meter.cross J.meter v)⟩
lemma vacant:Metered P D 0 w 0:=Metered.of_cast Medal.zeroT
lemma oneT:Metered P D 1 w 1:=Metered.of_cast Medal.oneT
lemma pile {I:Type*}(S: Finset I)(T:I→ Copy n)(A':I→ℝ)(h:∀ i∈S,Metered P D (T i) w (A' i)): Metered P D (∑ i∈S,T i) w (∑ i∈S,A' i):=by induction S using Finset.induction_on with|empty=>rw [sum_empty,sum_empty]; exact vacant|insert i S p ih => rw [sum_insert p,sum_insert p]; exact (h i (mem_insert_self ..)).link (ih fun j t=> h j (mem_insert_of_mem t))
lemma plot {I:Type*}(S: Finset I)(T:I→ Copy n)(A':I→ℝ)(h:∀ i∈S,Metered P D (T i) w (A' i))(s:0≤w): Metered P D (∏ i∈S,T i) w (∏ i∈S,A' i):=by induction S using Finset.induction_on with|empty=>rw [prod_empty,prod_empty]; exact oneT|insert i S p ih => rw [prod_insert p,prod_insert p]; exact (h i (mem_insert_self ..)).cross (ih fun j t=> h j (mem_insert_of_mem t)) s
include H in
lemma powered(v:0≤w):Metered P D (fun U=> exp (F U)-1) w (Real.exp a*a):= (Metered.of_cast (H.meter.expressT v)).related (fun V h=> by rw [unveil_F _ _ _ _ h])
end Metered
lemma stretch_P (F:InkD n)(X:Hub n)(e:PressB P X F w b)(hw:1≤ w): Metered P D (oV (numbE P.threshold X.val.2 F)) w (chi_f P.order*b):=by
  have he:=rimR e (zero_le_one.trans hw); by_cases k: Disjoint X.val.2 D
  · have hp:X.val.2 \∅ ⊆ univ\D:=by intro i t; refine mem_sdiff.mpr ⟨mem_univ _,?_⟩; exact Finset.disjoint_left.mp k (mem_sdiff.mp t).1
    refine (Metered.of_cast (he.stretchB (subset_univ _) (empty_subset _) hp)).related ?_; intro i u; symm
    apply Set.indicator_of_mem (show i.1∈_ from ?_); apply (shoreK _ i.1 u.1 _).1; unfold Healthy; rw [show flags _ _=D from u.2]; exact k
  refine (Metered.mono Metered.vacant (he.wage (zero_le_one.trans hw))).related ?_; intro i t; symm; apply Set.indicator_of_notMem (show i.1∉ _ from ?_); intro h; apply k; rw [←(show flags P.threshold i.1=D from t.2)]; exact ping_le (show pingS _ _ _ from h)
variable {Z:Type*}[TopologicalSpace Z]
lemma budget_E (X:RegBudget n)(u:IncX Q X P w b)(hw:1 ≤ w):∃ C:ℝ, ∀ D:Support (More n), Metered P D (oV (exponentL P X)) w C:=by
   obtain ⟨f,z,t⟩:=u.weight; refine ⟨∑ i:Hub n,chi_f P.order*f i,fun D=>?_⟩; let F(i:Hub n):=oV (numbE P.threshold i.val.2 (X i)); refine (Metered.pile univ F (fun i=>chi_f P.order*f i) (fun i _=>stretch_P P D _ _ (z i) hw)).related (fun i h=> ?_); simp only [Finset.sum_apply]; rfl
open Palot
lemma project_thr (U:Cusp n)(z:Aura n→ℝ)(h:Beau.Thr U z P w):Metered P D (fuelV P U) w (∑ i:Aura n with fuelH D i,z i):=by
 let T:= univ.filter (fun i:Aura n=>fuelH D i); let F(i:Aura n):= U i (D∩i.val); have he(i:Aura n) : Metered P D (F i) w (z i):= Metered.of_cast ((h i _).stretchB (subset_univ _) inter_subset_left (fun j k=> mem_sdiff.mpr ⟨mem_univ _,fun t=>(mem_sdiff.mp k).2 (mem_inter.mpr ⟨t,(mem_sdiff.mp k).1⟩)⟩)) -- arg order
 refine (Metered.pile T F z (fun i _=> he i)).related fun i u=> ?_; simp only [fuelV,show flags P.threshold i.1=D from u.2,Finset.sum_apply]; rfl
end YM.CF.Fixed.Voltage
