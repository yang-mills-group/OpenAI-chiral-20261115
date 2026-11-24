import YM.SU5.FiniteGaugeData.Tower.Cloaks
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
# Native gauge holds also on the step lift (no Protected equality hypotheses).
-/
open Fock Laurent Bloch Next.Free Fir Branch Tap Tenant Precision Drapes Vault Tree
open Reed (Fine think)
section subst
variable {N P : Side}

-- cleaner general; predicate Tset or complement both Slot invariant
private lemma at_color {i:Single N}(g:Seat N→SU.E)(B:Finset (Site N × SpinIdx))(s:Finset (Single N))(h:∀ j:Single N,j∈s↔ j.1∈ B)(p:i∈ s): withinM s (acts (tradew N g).val (basisKet i)):=by
 apply (within_test ..).2; rintro ⟨b,u⟩ t; rcases i with ⟨a,v⟩; rw [basis_act]
 have he:b≠a:=by rintro rfl; exact t ((h (b,u)).mpr ((h (b,v)).mp p))
 change jump (Equiv.refl _) (fun i=> (matter (g (node i.1))).val) (b,u) (a,v)=_
 rw [jump_apply,Equiv.refl_apply,if_neg he]
private lemma color_x {i:Single N}(g:Seat N→SU.E):
 (i∈Tset N→ withinM (Tset N) (acts (tradew N g).val (basisKet i)))∧(i∈(Tset N)ᶜ→ withinM (Tset N)ᶜ (acts (tradew N g).val (basisKet i))):=
 ⟨at_color g (univ.filter (fun i:Site N × SpinIdx=> i.2∈ plusHalf)) _ (fun j=>by rcases j with ⟨⟨a,b⟩,v⟩; simp [mem_Tset]),at_color g (univ.filter (fun i:Site N ×SpinIdx=> i.2∉plusHalf)) _ (fun j=>by rcases j with ⟨⟨a,b⟩,v⟩; simp [mem_Tset])⟩

-- Need Fine univ for multiplications after twist
lemma rotation_preserved{S:Finset (Single N)}{A:FC (Single N)}{b:Bool}(h:Fine (Tset N) S b A)(g:Seat N→SU.E):Fine (Tset N) univ b (twist (quantU (tradew N g)) A):=by
 induction h with
 | empty=> rw [map_zero]; exact .empty _
 | one=> rw [map_one]; exact .one
 | grow _ _ x y=> rw [map_mul]; exact .grow x y
 | add _ _ x y=> rw [map_add]; exact .add x y
 | scale _ c x=> rw [twist_scalar]; exact .scale x _
 | seed i p=>
    by_cases t:i∈ Tset N
    · rw [show (think (Tset N)).term i=Fock.put i from if_pos t,←create_put,twist_create]; exact fine_create _ ((color_x g).1 t) (within_univ _)
    rw [show (think (Tset N)).term i= -takeF i from if_neg t,map_neg,← remove_take,twist_remove]; exact fine_neg (fine_remove _ ((color_x g).2 (mem_compl.mpr t)) (within_univ _))

variable (G:Ratio N P)(j D:ℕ)(l': Stencil.LaurentRadius j G.count D)(o:Odd G.count.val)(M:Male)(Q:Haro.SpaceM){S:Finset (Single N)}{b:Bool}{A:FC (Single N)}(x:Fine (Tset N) S b A)
variable(z:Nom N P)(g:Seat P→SU.E)
local notation "T₀"=> tradew N (Peaks.scaleG G g)
local notation "T₁"=> tradew P g
local notation "F"=> subF G j Q.val M o
include l' x
lemma sub_gauge: (F (july G g z)) (twist (quantU T₀) A)=twist (quantU T₁) ((F z) A):=by
 induction x with
 | empty=> rw [map_zero,map_zero,map_zero,map_zero]
 | one=> rw [map_one,sub_one,sub_one,map_one]
 | add _ _ t v=> rw [map_add,map_add,map_add,map_add,t,v]
 | scale _ c v=> simp only [twist_scalar,map_smul,v]
 | grow a b t v=> rw [map_mul,sub_mul _ _ _ _ _ _ (rotation_preserved a _) (rotation_preserved b _),sub_mul _ _ _ _ _ _ a b,map_mul,t,v]
 | seed i h=>
    by_cases t:i∈ Tset N
    · rw [show (think (Tset N)).term i=put i from if_pos t,←create_put,twist_create,sub_create G j Q.val M o z (within_basis _ i t),sub_create G j Q.val M o _ ((color_x ..).1 t),twist_create,route_color G g j l' o M z true Q]
    have h:i∈(Tset N)ᶜ:= mem_compl.mpr t
    rw [show (think (Tset N)).term i= -takeF i from if_neg t,map_neg,map_neg,map_neg,map_neg,←remove_take,twist_remove,sub_remove G j Q.val M o z (within_basis _ i h),sub_remove G j Q.val M o _ ((color_x ..).2 h),twist_remove,route_color G g j l' o M z false Q]
end subst

section pushed
variable {N P : Side} (G:Ratio N P)(j D:ℕ)(l': Stencil.LaurentRadius j G.count D)(o:Odd G.count.val)(M:Male)(Q:Haro.SpaceM)(B:StepData (More N) (More P))(q:Chi)(β d:ℝ)(l:Loom N)
variable (v:B.ratio=ratio G)(t:B.patch.Branches B.kernel SU.group)(x:0<d)(y:2*d<YM.Next.SectorChange.firstRadius SU.group)
variable {S:Support (More N)}{b:Bool}{f:Mark N}(h:AtSupport b S f)(u:covariant f)
local notation "F"=> gathered G j Q.val M o q d f
include l' h u
lemma gather_G (g:Seat P→SU.E)(X:Fields N)(Y:Fields P): F (simultaneous g Y) (simultaneous (scaleG G g) X) = twist (quantU (tradew P g)) (F Y X):= by
 unfold gathered avgF Advance.before; simp_rw [u _ X,map_smul,map_sum] -- real linear map Alg.r?
 congr 1; refine sum_congr rfl fun T _=>?_; rw [show middle G q d T (simultaneous g Y) (simultaneous (scaleG G g) X)=july G g (middle G q d T Y X) from Prod.ext (brake_g G q d T o ..) rfl]
 exact sub_gauge G j D l' o M Q (h.allV X) (middle G q d T Y X) g
variable {V Z:ℝ}{R:ℕ}(z:Roof N V Z R l)
include z
omit l' h u
private def gaugeOrbit (N:Side)(g:Seat N→SU.E):Orbit N≃ᵐ Orbit N := ⟨⟨Girt.gird g, Girt.gird g⁻¹,by
    rintro ⟨x,y⟩; exact Prod.ext (show gauge g⁻¹ (gauge g x)=x from by rw [Sods.windy,inv_mul_cancel,Sods.windy_u]) (threads_T ..),by
    rintro ⟨x,y⟩; exact Prod.ext (show gauge g (gauge g⁻¹ x)=x from by rw [Sods.windy,mul_inv_cancel,Sods.windy_u]) (by simpa using threads_T g⁻¹ y)⟩, ((Wilson.prior_gauge g).measurable.comp measurable_fst).prodMk ((threads g).measurable.comp measurable_snd), ((Wilson.prior_gauge g⁻¹).measurable.comp measurable_fst).prodMk ((threads g⁻¹).measurable.comp measurable_snd)⟩
include l' h u v t x y
lemma gauge_pushed : covariant (pushMark G B j Q.val M o q d β l f):= by
 intro g D'
 let Y:=simultaneous g D'; let P':=scaleG G g; let θ:= gaugeOrbit N P'
 let T:= twist (quantU (tradew P g)); let T': FC (Single P)→L[ℝ] FC (Single P):= T.toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
 let w(H:Fields P)(V:Orbit N):= B.density β H.1 V.1 • F H (drawn l V)
 have hw:Integrable (w D') (Scree.city N):= Env.integrableX (Env.scale (Env.along (slice_env B β t D'.1) measurable_fst) (Env.along (g:=fun x : Orbit N=>(D',drawn l x)) (env_gathered G j Q.val M o q d l' x y f h.env) (measurable_const.prodMk (drawn_m l z.bill)))) _
 rw [outright G B j Q.val M o q d β l l' z.bill t x y _ h.env, outright G B j Q.val M o q d β l l' z.bill t x y _ h.env]
 change (∫ i:Orbit N,w Y i∂ Scree.city _)=T' (∫ i:Orbit N,w D' i∂ Scree.city _)
 have p:MeasurePreserving θ (Scree.city _) (Scree.city _):=(Wilson.prior_gauge P').prod (threads P')
 rw [←ContinuousLinearMap.integral_comp_comm _ hw, ←p.integral_comp' (w Y)]
 apply integral_congr_ae; refine Filter.Eventually.of_forall (fun i=> ?_); unfold w; dsimp only; rw [map_smul]; change B.density β (gauge g D'.1) (gauge P' i.1) • _= _ • twist (quantU (tradew P g)) (F D' _)
 rcases i with ⟨i,r⟩; rw [show drawn l (θ (i,r))= simultaneous P' (drawn l (i,r)) from Prod.ext rfl (z.rev i r P'),gather_G G j D l' o M Q q d h u]
 unfold P' Peaks.scaleG; rw [←v,B.covary t]
end pushed
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.gauge_pushed
