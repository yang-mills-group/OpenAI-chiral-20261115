import Bay.C.Topiary
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace C
open D hiding quiver
open Exterior Precision Nacre
open scoped ContDiff


open Forge Pressure

variable {N:Side}
lemma wakeLe (z:Finset (Bond (More N)))(x:tangD N)(i:Bond (More N)):‖wakeB z x i‖≤‖x‖:=by
 rw [Forge.steadyB]
 split
 · exact norm_le_pi_norm _ _
 rw [norm_zero]; exact norm_nonneg _

abbrev gustLinks(k:ℕ)(T:ℝ):Prop:=
 ∀ {N: Side} (z:Finset (Bond (More N)))(v:Pane N)
   (x:tangD N),‖x‖≤1 → TransK k (Forge.gyrate z v) x T

lemma breeze (k:ℕ):∃ T:ℝ,1≤T∧gustLinks k T:=by
 obtain ⟨p,h,H⟩:=compact_allow k zero_le_one D.fire (fire_paid.of_le le_top)
 let V:=composeCost k p 1
 let T:=max V 1
 refine ⟨T,le_max_right ..,?_⟩
 intro N z v x hx i
 let a:Op SU.F:= fund (v i)
 have ht:‖a‖≤1:=(Sods.tone (v i).val).le
 let L : Op SU.F →L[ℝ] Op SU.F :=(ContinuousLinearMap.mul ℝ (Op SU.F)).flip a
 have hl:‖L‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y=>
    (norm_mul_le y a).trans ((mul_le_of_le_one_right (norm_nonneg _) ht).trans_eq (one_mul _).symm)
 let W:tangD N →L[ℝ]Øc:=(ContinuousLinearMap.proj i).comp (wakeB z)
 have w:‖W‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    fun y=>(wakeLe z y i).trans_eq (one_mul _).symm

 have pW: ‖W x‖≤1:=(wakeLe z x i).trans hx
 have y: Allows k (fun x=>D.fire (W x)) x V := (H _ pW).comp (allows_linear w pW)
 have t:= y.linear L hl
 rw [one_mul] at t
 exact t.mono (le_max_left ..)

abbrev gustBase(k:ℕ)(T:ℝ):Prop:=
 ∀ {N:Side} (z:Finset (Bond (More N))) (v:Pane N)
    (x:tangD N), ‖x‖ ≤1→ Allows k (profile ∘ Forge.gyrate z v) x T

lemma gust (k:ℕ):∃ T:ℝ,1≤T∧gustBase k T:=by
 obtain ⟨T,h,g⟩:=breeze k
 obtain ⟨Y,j,V⟩:=Proa.profile_X k T (zero_le_one.trans h)
 refine ⟨max Y 1,le_max_right ..,?_⟩
 intro _ z v x hx;exact (V _ x (g z v _ hx)).mono (le_max_left ..)

variable {d T:ℝ}{k:ℕ}
lemma blows (g:gustBase 6 T)
 (z:Finset (Bond (More N))) (v:Pane N)(x:tangD N)(h:‖x‖≤1): ‖profile (gyrate z v x)-profile v‖ ≤ T*‖x‖:=by
 let f:=profile ∘ gyrate z v
 have a:=convex_closedBall (0:tangD N) 1
 have p:=a.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=f)
   (fun i b=> (g z v _ (mem_closedBall_zero_iff.mp b)).smooth.differentiableAt (by norm_num))
   (fun i b=> by rw [←norm_iteratedFDeriv_one]; exact
      (g z v _ (mem_closedBall_zero_iff.mp b)).norm_le _ (by decide))
   (Metric.mem_closedBall_self (zero_le_one)) (mem_closedBall_zero_iff.mpr h)
 unfold f at p
 simpa only [comp_apply, Forge.born,sub_zero] using p

abbrev glaze (V:SOp N) (z:Chin N):= Matrix.trace (V z)
lemma glazeCap {o:Seat N}{V:SOp N}{a b:ℝ} (A:Trunk o V k a b d)(p:0≤a):
 let f:GateR N d→ℂ:=fun z=>glaze V z.val
 Looks _ f ∧ Continuous f ∧ ∀i,‖f i‖≤ b:=by
 intro f
 obtain ⟨X,C,q,t,r,u⟩:=A.home
 have h(i): f i=∑j:Sa N,pic (X j) i:=by unfold f glaze; rw[u, Matrix.trace_sum]; rfl
 rw [funext h]
 refine ⟨fun s p v w=>?_,continuous_finsetSum _ (fun i _=> (essay_looks (q i)).2.1),fun i=>?_⟩
 · unfold Function.comp
   convert (DifferentiableOn.sum (𝕜:=ℂ) (s:=s) (u:=univ) (A:=fun i x=>pic (X i) (v x)) (fun i _=> (essay_looks (q i)).1 _ p _ w)) using 1 <;> try rfl
   funext x;rw [Finset.sum_apply]
 apply le_trans (norm_sum_le ..)
 refine (sum_le_sum (fun j (_:j∈univ)=> ((essay_looks (q j)).2.2 i).trans (le_mul_of_one_le_left
      (show 0≤ledgerV (C j) from sum_nonneg fun y _=>sum_nonneg fun z _=> (q j).nonn y z) (rent_one p j)))).trans r

abbrev glazeH (d:ℝ)(V:SOp N) (z:Config SU.group (More N)) :=
   equalizer (fun y:GateR N d=>glaze V y.val) (profile z)
structure Luster (d D r:ℝ): Prop where
 dp:0<D
 rp:0<r
 pay {N:Side}{o:Seat N}{k:ℕ}{a b:ℝ}
  {V:SOp N} (A:Trunk o V k a b d) (p:0≤a)(v:Pane N)
  (l:Guard v d)(z:Finset (Bond (More N))) (x:tangD N) :
   ‖x‖≤r → Allows 6 (glazeH d V ∘ Forge.gyrate z v) x (D*b) ∧
       profile (Forge.gyrate z v x) ∈ GateR N d

lemma sheen (p:0<d):∃ D r,Luster d D r:=by
 obtain ⟨T,w,g⟩:= gust 6
 have hT:=zero_lt_one.trans_le w
 let r:=min 1 ((d/2)/T)
 have e:0<r:=lt_min zero_lt_one (by positivity)
 let A:=(1+2^(6:ℕ)/(d/2))^(6:ℕ)
 refine ⟨composeCost 6 A T,r,⟨by unfold composeCost A; positivity,e,?_⟩⟩
 intro N o k a b V B a0 v l z x h
 have hx:‖x‖≤1:=h.trans (min_le_left ..)
 let y:=profile (gyrate z v x)
 have hh: ‖y-profile v‖ ≤ d/2:= (blows g z v x hx).trans 
     (mul_comm _ ‖x‖ ▸ (le_div_iff₀ hT).mp (h.trans (min_le_right ..)))

 have hb:ball y (d/2)⊆ GateR N d:= by
     intro i j
     rw[mem_ball_iff_norm] at j
     exact ⟨v,l,(norm_sub_le_norm_sub_add_norm_sub _ y _).trans_lt 
         ((add_lt_add_of_lt_of_le j hh).trans_eq (add_halves _))⟩
 obtain ⟨ha,j,t⟩:=glazeCap B a0
 have u:=half_pos p
 have m:=allows_looks ha j hb u 6 t
 refine ⟨?_,hb (mem_ball_self u)⟩
 exact ((show Allows 6 _ ((profile ∘ gyrate z v) x) _ from m).comp 
    (g _ _ _ hx)).mono (by unfold composeCost A;exact le_of_eq (by ring))
