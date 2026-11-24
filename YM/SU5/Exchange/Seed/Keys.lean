import YM.CF.Mew.Pot
import YM.SU5.Exchange.Seed.Gain
import YM.SU5.Exchange.Seed.Mono
import YM.CF.Stax.Render
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
local notation "CΞ"=> Cipher n
variable (P: BudgetPoint)(h:ℝ)(δ:ℕ)
variable {P h δ}
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
-- Layered Key-jet matching: issue the untruncated R but pay/apply layers only.
open Mew PowerSeries
open scoped YM.CF.Mew
variable {J:Type}[LinearOrder J][Fintype J]
variable (K:Key J→Rinse (Seat n) (Copy n))(z b:Aura n→ℝ)
variable {M:Key J→Orbit n→Aura n→ FC (Dwell n)} (T:∀ v∈hill J,Pitch P h δ (K v) z (M v))
variable (w:0≤h)(x:Orbit n)(p:FleetS P.threshold x.1)
local notation "Ωx"=> flags P.threshold x.1
-- K motion can be linear per key before Feed (incl under tag policy)
def Gamble : Prop:=∀ (X:Aura n),∀ D⊆X.val,∀ Y:Aura n, Y.val⊆X.val→∀ (i:ℕ) (F:Key J→ Copy n),Solvent i F → Solvent (i+1) fun v=> K v X D Y (F v)
variable (m:Gamble K)
local notation "Qk" z:max=> chip (K z) F
local notation "Hc"=> hoop -- dummy
section homo
-- note induction on the COSTED part only; invalid D not used.
include m
lemma chipsSol (X:Aura n)(D:Support (More n))(u:D⊆X.val)(i:ℕ):Solvent i (fun z=>coeff i (Cadre.chip (K z) F X D)):=by
 induction i using Nat.strong_induction_on generalizing X D with
 |h i ih=>
   cases i with
   |zero=> simp_rw [Cadre.peg]; exact Solvent.still _
   |succ i=>
    have hx(v:Key J): coeff (i+1) (Cadre.chip (K v) F X D)=((↑(((i:ℝ)+1)⁻¹)):ℂ) • (∑ Y:VX,∑ G∈drum X Y D,K v X D Y (coeff i (∏ j∈G,Cadre.chip (K v) F j (D∩j.val)))):=by
       rw [Complex.coe_smul,←ore]; nth_rw 1 [Cadre.peel]; rw [Cadre.sprig]
    simp_rw [hx]; apply Solvent.smul; apply Solvent.sum; intro Y _; apply Solvent.sum; intro G u0; apply m _ _ u _ (by rw [(drum_p ..|>.mp u0).2.2]; exact subset_union_left)
    simp_rw [coeff_prod]; apply Solvent.sum; intro j v; let n(k:VX):= j k; have ht:(∑ k∈G,n k)=i:= (mem_finsuppAntidiag.mp v).1
    exact ht ▸ Solvent.prod (J:=VX) G _ n (fun k s=> ih (j k) (Nat.lt_succ_of_le ((single_le_sum (fun _ _=>Nat.zero_le _) s).trans_eq ht)) _ _ inter_subset_right) -- ht ▸ e replaces expression RHS reducing? tune
local notation "Zq" z:max=> cumQ F (K z) x P
lemma atSlot (X:Aura n)(i:ℕ):Solvent i (fun z=> coeff i (cumQ F (K z) x P X)):=by
 let V:Copy n →ₗ[ℂ] Cipher n:= LinearMap.proj x
 simp_rw [cumQ,fP]; exact Solvent.map V (chipsSol F K m _ _ inter_subset_right i)
end homo
local notation "Zq" z:max=> cumQ F (K z) x P
section
-- ψ of finite sketch. homogeneous term.Collectors
variable {I N:Type*}[Fintype I][DecidableEq I][NormedCommRing N][NormedAlgebra ℂ N][CompleteSpace N]
variable (S:Finset I)(Fz:Key J→ I→PowerSeries N)
variable (hSol:∀ (k:ℕ) i, Solvent k (fun z=> coeff k (Fz z i)))
lemma solρ (p:∀ (k:ℕ) i, Solvent k (fun z=> coeff k (Fz z i))) (i:ℕ):Solvent i (fun z=>coeff i (∏ j∈S,Fz z j)):=by
 simp_rw [coeff_prod]; apply Solvent.sum; intro j v
 let K(k:I):= j k; have ht:(∑ k∈S,K k)= i:= (mem_finsuppAntidiag.mp v).1
 exact ht ▸ (Solvent.prod S (fun k z=>coeff (K k) (Fz z k)) K (fun k _=>p ..))
-- expansion truncation not needing infinite analycity. power-series truncated layer.Before M4 cQ.
private def trΛ (F:PowerSeries N)(i:ℕ):PowerSeries N:=PowerSeries.mk fun j=> if j ≤ i then coeff j F else 0
private lemma cost_η (F:PowerSeries N)(k j:ℕ): coeff j (trΛ F k)=if j≤k then coeff j F else 0:=by rw [trΛ,coeff_mk]
private lemma hit_bound(F:PowerSeries N)(i:ℕ)(p:∀ j, i<j → coeff j F=0): Aqua F ∧ hitU F= (∑ k∈ Finset.range (i+1),coeff k F):=by
 refine ⟨summable_of_ne_finset_zero (s:=Finset.range (i+1)) (fun j v=> ?_), tsum_eq_sum (s:=Finset.range (i+1)) (fun j h=> p j (by rw [mem_range,not_lt] at h; omega))⟩ -- f sum
 -- which v? tune
 rw [p j (by rw [mem_range,not_lt] at v; omega),norm_zero]
private lemma hit_Λ (F:PowerSeries N)(i:ℕ): Aqua (trΛ F i)∧ hitU (trΛ F i)=∑ k∈ range (i+1),coeff k F:=by
 obtain ⟨p,t⟩:= hit_bound (trΛ F i) i (fun j v=> (cost_η F i j).trans (if_neg (not_le.mpr v))); rw [t]
 exact ⟨p,(sum_congr rfl fun j u=>(cost_η ..).trans (if_pos (by rw [mem_range] at u; omega)))⟩
private lemma hit_prod (E:I→PowerSeries N)(i:ℕ) : (∏ j∈ S,(∑ k∈range (i+1),coeff k (E j)))=∑ k∈range (i*S.card+1), coeff k (∏ j∈ S,trΛ (E j) i):=by
 let U(j):= trΛ (E j) i; let P:= ∏ j∈S,U j; have he := Aqua.ψ_m S U (fun j _=>(hit_Λ (E j) i).1)
 have hx: (∏ j∈S,(∑ k∈range (i+1),coeff k (E j)))=hitU P:=by simp_rw [← (hit_Λ (E _) i).2]; exact he.2.symm
 rw [hx]; refine (hit_bound P _ (fun j v=>?_)).2
 unfold P; rw [coeff_prod]; apply Finset.sum_eq_zero; intro a u
 obtain ⟨k,x,q⟩:∃ k∈S,i<a k :=by
    by_contra! h; have hv:= (mem_finsuppAntidiag.mp u).1; have hG:=sum_le_sum h; rw [sum_const,hv,smul_eq_mul,mul_comm] at hG; omega -- h ∀ k k∈S→ ..
 exact prod_eq_zero x ((cost_η ..).trans (if_neg (not_le.mpr q)))
include hSol
lemma leg_Ρ (i:ℕ) (l: List J)(v:l.length ≤ i) : let f(z:Key J):= (∏ j∈ S,Fz z j); let zN(a:Key J)(j:I):=∑ k∈Finset.range (i+1),coeff k (Fz a j); River (fun z=>∏ j∈ S, zN z j) ∧
 tipI (fun z=>∏ j∈ S, zN z j) l=tipI (fun z=>coeff l.length (f z)) l:=by
 intro f zN; let U(v:Key J)(i':I):= trΛ (Fz v i') i; let F'(z):=(∏ j∈S,U z j)
 have ht(z:Key J):(∏ j∈S, zN z j)=(∑ k∈range (i*S.card+1),coeff k (F' z)):= hit_prod S (Fz z) i
 let k:= l.length
 have hu(v:Key J): coeff k (F' v)=coeff k (f v):=by
    unfold f F'; rw [coeff_prod,coeff_prod]; refine sum_congr rfl fun j p=> prod_congr rfl (fun Y t=> (cost_η (Fz v Y) i (j Y)).trans (if_pos (((single_le_sum (fun a _=>Nat.zero_le (j a)) t).trans_eq (mem_finsuppAntidiag.mp p).1).trans (by assumption: k ≤ i))))
 have hs(n:ℕ):Solvent n (fun z=> coeff n (F' z)):= by apply solρ S U _ n; intro a b; unfold U; simp_rw [cost_η]; split_ifs; exact hSol a b; exact Solvent.zero a
 rw [funext ht]
 have h:=tip_bank (range (i*S.card+1)) (fun k z=>coeff k (F' z)) (fun i _=>(hs i).riv); refine ⟨h.1,?_⟩; rw [h.2,sum_eq_single k, show (fun z=> coeff k (F' z))=_ from funext hu]
 · intro j w g; exact (hs j).skip l (Ne.symm g)
 intro L; have g:¬ S.Nonempty:=by intro u; apply L; rw [mem_range]; apply Nat.lt_succ_of_le; exact v.trans (Nat.le_mul_of_pos_right _ (card_pos.mpr u)) -- tune
 rw [not_nonempty_iff_eq_empty.mp g] at L; have he:k≠0:=by simp only [mem_range,card_empty,Nat.mul_zero, Nat.zero_add, Nat.lt_one_iff] at L; exact L -- simp Nat.lt_one...
 unfold F'; simp_rw [not_nonempty_iff_eq_empty.mp g,prod_empty,coeff_one,if_neg he]; exact tip_0 l
end
section
local notation "QZ"=> fun z:Key J=> cumQ F (K z) x P
include w p m hF T
-- Any z within hill, absolute.M4 all poses eventually. project to physical CANARY
lemma concreteTip (H:Wave (Dwell n)→L[ℂ]Wave (Single n))(U:Key J→ FC (Single n)) (l:List J) (i:ℕ)(e:l.length ≤ i)
 (u:∀ z∈hill J,∀ X: Wave (Dwell n),H (acts (∑ Y:Aura n,M z x Y) X)=acts (U z) (H X)) :
 tipI (fun z=> H (Cadre.poseL _ (hGas Ωx (hailV Ωx (layerN F (K z) i) x)))) l=
 tipI (fun z=> acts ((((l.length.factorial:ℂ)⁻¹)) • (U z)^l.length) (H (Cadre.poseL _ (hGas Ωx (Vow.hailV Ωx F x))))) l:=by
 let O:= Ωx; let A(z:Key J):= QZ z; let f(S:Finset (Aura n))(z:Key J):=∏ j∈S,A z j; let g(S:Hk)(z:Key J):=∏ j∈S,hailV O (layerN F (K z) i) x j
 let U':=stream O; have wq:z=z:=rfl -- z argument unused removed??
 have hu(j a):= atSlot (P:=P) F K x m a j
 have h(S:Hk):= leg_Ρ S A hu i l e
 have ht(S:Hk)(v:Key J):g S v=(∏ j∈S,(∑ k∈range (i+1),coeff k (A v j))):=by
    unfold g; simp only [hailV,layerN, Finset.sum_apply, A,cumQ,fP]; rfl
 have hS(S:Hk): River (g S)∧ tipI (g S) l=tipI (fun z=> coeff l.length (f S z)) l:=by rw [funext (ht S)]; exact h S
 let F₁:=fun z=> (∑ S∈U',g S z); let V:= fun z=> coeff l.length (∑ S∈U',f S z); let L: Cipher n→ₗ[ℂ] Wave (Single n):=⟨⟨fun z=> H (Cadre.poseL _ z), fun a b=> by change H _ = H _ +_; rw [←map_add]; exact congrArg H (act_add ..)⟩,fun a b=> (congrArg H (act_smul ..)).trans (map_smul ..)⟩ -- tune add types infer
 have wB:River V:=by
    unfold V; simp_rw [map_sum]; exact (tip_bank U' (fun S z=> coeff l.length (f S z)) (fun i _=> (solρ i A hu _).riv)).1
 have wΨ:= tip_bank U' g (fun S _=> (hS S).1); let R(v):=L (F₁ v); have ht':tipI F₁ l=tipI V l:=by
    unfold V F₁; simp_rw [map_sum]; rw [wΨ.2]; exact (sum_congr rfl (fun i _=>(hS i).2)).trans ( (tip_bank U' (fun S z=>coeff l.length (f S z)) (fun S _=>(solρ S A hu l.length).riv)).2 _).symm
 change tipI R _= _; rw [show tipI R l=L (tipI F₁ l) from sim_H wΨ.1 L.toContinuousLinearMap l roots,ht']
 let f'(z:Key J):= L (V z); rw [←show tipI f' l=L (tipI V l) from sim_H wB L.toContinuousLinearMap l roots]; apply lace_C l (fun j t=> ?_) roots
 refine (ledger_n F r hF (K j) _ (T j t) w x p H (U j) (u j t) l.length).trans (congrArg (fun v=> acts _ v) (congrArg H (show Cadre.pose _ 0 =_ from ?_)))
 -- pose const
 unfold Cadre.pose; rw [Cadre.car_v,Stax.star_L F r hF (K j) _ (T j t) w x p]
end
end YM.CF.Stax
