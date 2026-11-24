import Bay.D.Atlas
import Bay.D.Resin
import YM.Work.E01
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

namespace D
open Exterior Precision Nacre
open scoped ContDiff

open Work.F03
abbrev Pureton:=PlaqAxes × group.ColorIndex
abbrev Cella(n:Side):=Site n × Pureton
abbrev tulipF {n:Side} (i:Cella n):Pressure.Cell n:=(i.1,i.2.1)
variable {n N:Side}

def brine{n:Side}(y:fieldDir group n 1)(i:Cella n):ℝ:= faceCurl (tulipF i) y i.2.2
-- ℓ² color norm, pay with ℓ² cut. 
def fen (s:Support n):Finset (Cella n):= s ×ˢ univ
def canal(s:Support n): (fieldDir group n 1)→ₗ[ℝ]Rink (Cella n) where
 toFun y:= WithLp.toLp 2 fun i=> if i.1∈ s then brine y i else 0
 map_add' x y := by 
   ext1 i;rw[WithLp.ofLp_add,Pi.add_apply]
   simp only
   by_cases h:i.1∈s <;> simp only [h,ite_true,ite_false,add_zero] 
   exact congrFun (Matrix.mulVec_add (d 1 n) (parts group 1 x i.2.2) (parts group 1 y i.2.2)) (i.1,plaquette i.2.1)
 map_smul' t x:=by
   ext1 i;rw[WithLp.ofLp_smul,Pi.smul_apply]
   simp only

   by_cases h:i.1∈s<;>simp only[h,ite_true,ite_false,smul_zero]
   exact congrFun (Matrix.mulVec_smul (d 1 n) t (parts group 1 x i.2.2)) (i.1,plaquette i.2.1)
variable {s:Support n}
lemma canal_f(y:fieldDir group n 1)(i:Cella n): canal s y i ≠ 0→i∈fen s:=by
 change (if i.1∈s then brine y i else 0)≠0→_
 by_cases h:i.1∈s <;>simp[h,fen]
lemma curl_f{j:Pressure.Cell n}(h:j.1∈s)(y:fieldDir group n 1):
     ‖faceCurl j y‖≤‖canal s y‖:=by
 apply le_of_sq_le_sq _ (by positivity)
 rw[EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
 let f(i:group.ColorIndex):Cella n:=(j.1,(j.2,i))
 rw[Fintype.sum_prod_type]
 apply le_trans _ (single_le_sum (f:=fun a:Site n=> ∑u:Pureton, ‖canal s y (a,u)‖^2)
   (fun a _=>by positivity) (mem_univ j.1))
 rw[Fintype.sum_prod_type]
 apply le_trans _ (single_le_sum (f:=fun a:PlaqAxes=> ∑u:group.ColorIndex, ‖canal s y (j.1,a,u)‖^2)
   (fun a _=>by positivity) (mem_univ j.2))
 refine sum_le_sum (fun i _=>le_of_eq ?_)
 have he:canal s y (f i)=faceCurl j y i:=by change (if j.1∈s then _ else _) = _;rw[if_pos h];rfl
 exact congrArg (fun x:ℝ=>‖x‖^2) he.symm
lemma curl_chord(j:Pressure.Cell n)(y:fieldDir group n 1):
     Tendsto (fun t:ℝ=> group.chord (faceValue (represent (t • y)) j) / t)
       (𝓝[>] 0) (𝓝 (‖faceCurl j y‖)):=by
 have e:= price_limit (V:=fun t=>faceValue (represent (t • y)) j)
    (by simp only [zero_smul]; exact Push.stroll_zero ..) (face_deriv j y)
 have h:= (e.mono_left (nhdsGT_le_nhdsNE 0)).mul_const 2
 rw[div_mul_cancel₀ _ two_ne_zero] at h
 have he:=h.sqrt
 rw[Real.sqrt_sq (by positivity:0≤ ‖faceCurl j y‖)] at he
 refine he.congr' ?_
 filter_upwards [self_mem_nhdsWithin] with t ht
 have hp:t≠0:=(show 0<t from ht).ne'

 symm
 rw[←Real.sqrt_sq (div_nonneg (group.chord_nonneg _) (show 0≤t from le_of_lt ht))]
 congr 1
 rw [div_pow,group.chord_price]
 ring


variable {o:Seat N}{k:ℕ}

abbrev Lagoon(k:ℕ)(o:Seat N):= fen (roost (k+3) o)
lemma cure {b:ℝ}(y:Lag N)
    (h:‖canal (roost (k+3) o) y‖<b):
    ∀ᶠ t:ℝ in 𝓝[>] 0, Healthy (t*b) (roost (k+1) o) (represent (t • y)):=by
 have hv:∀ᶠ t:ℝ in 𝓝[>] 0,∀ j:Pressure.Cell (More N), j.1 ∈ roost (k+3) o →
      group.chord (faceValue (represent (t • y)) j) ≤ t*b:=by
    refine eventually_all.mpr fun j=>?_
    by_cases ht:j.1∈roost (k+3) o
    · filter_upwards [(curl_chord j y).eventually (gt_mem_nhds ((curl_f ht y).trans_lt h)),self_mem_nhdsWithin] with t hh hp _
      rw[mul_comm]
      exact ((div_le_iff₀ (show (0:ℝ)<t from hp)).mp hh.le)
    simp[ht]
 filter_upwards [hv] with t g
 refine Finset.disjoint_left.mpr fun x e hx=>?_
 obtain ⟨j,u,q⟩:=(flags_spec ..).mp hx
 apply (g j ?_).not_gt q
 have a:=Work.E01.sep_touched j x u
 have he: j.1∈ Lattice.halo 2 (roost (k+1) o):=halo_spec.mpr ⟨x,e,by first|exact a|rw [separation_comm];exact a⟩
 exact chainR (by omega) he

variable {d D r:ℝ}{F:Plank N d}{S:Sa N}{C:Toll (Single N)}
def melt(D:ℝ)(k:ℕ):ℝ:=D*(8*(1+(k:ℝ)))^2
lemma denizen
   (p:Twine 3 d D r)(q:Essay S C F)
   (j:∀i∈S,separation o i≤k)
   (w:2*(k+1)<(More N).val):
   Crate (Lagoon k o) (canal (roost (k+3) o)) (tremble (picL F)) (melt D k*ledgerV C):=by
 have hv:0 ≤ melt D k*ledgerV C:= mul_nonneg (mul_nonneg p.dp.le (sq_nonneg _)) (credit_pos q)
 refine ⟨hv,fun _ _ e=>canal_f _ _ e, tremble_sym ((touch p q).self p.rp),fun y=>?_⟩
 let c:=‖canal (roost (k+3) o) y‖
 have ht (b:ℝ)(h:c<b): ‖quiver (picL F) y‖ ≤ melt D k*ledgerV C*b^2:=by
   have hz:∀ᶠ t:ℝ in 𝓝 0, frosty k (t*b) ≤ iceR r ∧ ‖t • y‖≤r:=by
       have ha:= (show ContinuousAt (fun t:ℝ=>frosty k (t*b)) 0 from by unfold frosty;fun_prop).eventually
         (ge_mem_nhds (by simpa [frosty] using ice_pos p.rp:frosty k (0*b) < iceR r))
       have h₁ : ‖(0:ℝ) • y‖ <r:=by simpa using p.rp
       exact ha.and ((show ContinuousAt (fun t:ℝ=>‖t • y‖) 0 from by fun_prop).eventually (ge_mem_nhds h₁))

   apply le_of_tendsto (((touch p q).limit p.rp y).norm)
   filter_upwards [eventually_nhdsWithin_of_eventually_nhds hz, cure y h, self_mem_nhdsWithin] with t u a e
   have lt:(0:ℝ)<t:=e
   have hp:0<b:=(norm_nonneg _).trans_lt h
   rw[norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
   have h₃:=bright p q ((p.pay F q _ u.2).2) (fun _ _ _=>rfl) j a (mul_nonneg lt.le hp.le) u.1 w
   refine (mul_le_mul_of_nonneg_left h₃ (sq_nonneg _)).trans_eq ?_
   unfold frosty melt; field_simp
 exact ge_of_tendsto (f:=fun b=>melt D k*ledgerV C*b^2)
    ((show ContinuousAt (fun b=>melt D k * ledgerV C * b^2) c from by fun_prop).tendsto.mono_left
       (show 𝓝[>] c ≤ 𝓝 c from nhdsWithin_le_nhds)) (by filter_upwards [self_mem_nhdsWithin] with t h; exact ht t h)

lemma myrtle
   (p:Twine 3 d D r)(q:Essay S C F)
   (j:∀i∈S,separation o i≤k)
   (w:2*(k+1)<(More N).val):
   ∃ A, Rake (Lagoon k o) (2*(melt D k*ledgerV C)*(Lagoon k o).card^2) A ∧
   ∀ x:Lag N, quiver (picL F) x = splash A (brine x) :=by
 obtain ⟨A,h,H⟩:=(denizen p q j w).slush
 refine ⟨A,h,fun x=>?_⟩
 have he:Set.EqOn (fun i=>canal (roost (k+3) o) x i) (brine x) (Lagoon k o):=
    fun _ e=>if_pos (Finset.mem_product.mp e).1
 exact (H x).trans (h.swirl_same he he)
lemma lake_mono{j:ℕ}(h:k≤j): Lagoon k o⊆Lagoon j o:=fun _ u=> mem_product.mpr
  ⟨roost_expand (Nat.add_le_add_right h 3) (mem_product.mp u).1, (mem_product.mp u).2⟩

end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.myrtle
