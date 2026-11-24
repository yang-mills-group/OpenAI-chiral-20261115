import YM.SU5.Selected.Airy.Window
import YM.CF.Lattice.Reference
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Topology Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset Fock Rush Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
local instance : CompactSpace grounds:= isCompact_iff_compactSpace.mp groundsCompact
-- bit endemic coe. Need extending inverse only and walls. Work any sites in support counts not patch-stretching.
lemma pi_repeated {u v:ℕ}{c:Facet3}(p:4≤u)(z:c∈grounds): ContinuousWithinAt (fun x:Facet3=> (trove x true u v)⁻¹) grounds c:= by
 let F(x:Facet3):= trove x true u v
 have h:Continuous (fun x:grounds=> F x.val) := continuous_matrix fun i j=> (continuousOn_iff_continuous_restrict.mp (legs true (u+i.val+j.val))) -- signature
 have hp:IsUnit (F c).det:= (Matrix.isUnit_iff_isUnit_det (F c)).mp (fit c true u v p z) -- ellipsis before!
 have e: ContinuousAt (Ring.inverse) (F c).det:= by simp_rw [show Ring.inverse (M₀:=ℂ)= Inv.inv from funext (fun a=> Ring.inverse_eq_inv a)]; exact continuousAt_inv₀ hp.ne_zero -- name
 exact (continuousAt_matrix_inv _ e).comp_continuousWithinAt ((continuousOn_iff_continuous_restrict.mpr h) c z)
lemma camber (u v:ℕ)(e:4≤u): ∃ V:Torch→ Op (Fin v), Continuous V∧∀ x∈grounds,V (road x)=(trove x true u v)⁻¹:=by
 let F(x:grounds):= (trove x.val true u v)⁻¹
 have h : Continuous F:= continuousOn_iff_continuous_restrict.mp (fun x z=> pi_repeated e z)
 letI : TietzeExtension.{0} (Op (Fin v)):= inferInstanceAs (TietzeExtension.{0} (Fin v→Fin v→ℂ))
 obtain ⟨V,t⟩:= ContinuousMap.exists_extension' road_plant (⟨F,h⟩ : C(_, _))
 exact ⟨V,map_continuous V, fun x z=> congrFun t ⟨x,z⟩⟩
private lemma fireworks : ∃ V: Coast→ Momentum, Continuous V∧∀ x∈grounds,∀ t:roundC,V (Ε (road x) t)= walls x t:=by
 haveI hF:TietzeExtension.{0} Momentum:=inferInstanceAs (TietzeExtension.{0} (Axis→ℂ))
 let F(x:grounds × roundC):= Ε (road x.1.val) x.2
 have hp (x): pier (F x)= road x.1.val:= here_p ..; have hl(x): lapse (F x)=x.2:= here_l ..
 have h: IsClosedEmbedding F:=by
    have h: Continuous F:=by
        apply continuous_pi; intro i; cases i using Fin.lastCases with| last=> simp only [F,Ε,Fin.snoc_last]; fun_prop|cast i=> simp only [F,Ε,Fin.snoc_castSucc]; exact (continuous_apply _).comp (road_plant.continuous.comp continuous_fst)
    refine h.isClosedEmbedding ?_; intro x y a; apply Prod.ext (road_plant.injective ?_) ?_
    · exact (hp x).symm.trans ((congrArg pier a).trans (hp y)) -- unfold implicit
    exact (hl x).symm.trans ((congrArg lapse a).trans (hl y))
 obtain ⟨V,t⟩:= ContinuousMap.exists_extension' h (⟨(fun k:grounds×roundC=>walls k.1.val k.2), walls_walk⟩: C(_,_))
 exact ⟨V,map_continuous V, fun x z t'=> congrFun t (⟨x,z⟩,t')⟩
def utility (w:Coast): Momentum:= fireworks.choose w
@[fun_prop] lemma utility_c : Continuous utility:= fireworks.choose_spec.1
lemma utility_spec (x:Facet3)(e:x∈grounds)(t:roundC) : utility (Ε (road x) t)= walls x t:= fireworks.choose_spec.2 x e t
-- visible exact upper & approxim. potential choose up row=0, strip interior layers from 0..
variable (G:Side)(n p:ℕ) (h:n≥4)
abbrev Wq := WRect SpinIdx (Fin p)
def forge (a:SpinIdx)(x:Fin p→ℂ):Wq p:= Matrix.of fun i j => if a=i then x j else 0
local notation "A" => Aop
-- stencil semantics signs: Fourier symbol multiplies at momentum, mode d -> support row x if col=x+wrap(d), hence support at column center MINUS character index. X later (n+i), Y earlier (-j). gram temporal integral in *positive* frequency. No loss offset.
def strikeL (i:Fin p) : ℤ:= (↑(n+i.val:ℕ))
def strikeE(i:Fin p): ℤ := - (i.val:ℤ)
-- raw same Soap amplitudes; extending. normalize later for ace.
def nails(t:roundC):Wq p:= forge p 2 (fun i=> fourier (-(strikeL n p i)) t)
def staves(t:roundC):Wq p:= forge p 0 (fun i=> fourier (-(strikeE p i)) t)
@[fun_prop] lemma nails_c :Continuous (nails n p):= continuous_matrix fun i j=>by unfold nails forge; simp only [Matrix.of_apply]; split_ifs <;> fun_prop
@[fun_prop] lemma staves_c :Continuous (staves p):= continuous_matrix fun i j=>by unfold staves forge; simp only [Matrix.of_apply]; split_ifs <;> fun_prop
lemma nails_minus (t:roundC): (1-A)*nails n p t=nails n p t:=by
 rw [Adef,←Lat.raising,← dim_cut]; ext i j; rw [cutM,Matrix.diagonal_mul]; fin_cases i <;> simp (config:={decide:=true}) [nails,forge] -- tune
lemma staves_plus (t:roundC): A*staves p t=staves p t:=by
 rw [Adef, ← Lat.raising]; ext i j; rw [cutM,Matrix.diagonal_mul]; fin_cases i <;> simp (config:={decide:=true}) [staves,forge]
def screens (w:Torch):= (↑(φ:ℝ):ℂ) • (camber n p h).choose w
def children (w:Coast): Wq p:= (soap G (pier w):ℂ) • nails n p (lapse w)
def plinth(w:Coast): Wq p:= (soap G (pier w):ℂ) • (staves p (lapse w) * screens n p h (pier w))
def artisans(w: Coast):Wq p:= (1-zen (utility w))*plinth G n p h w
lemma plinth_plus (w:Coast): A*plinth G n p h w=plinth G n p h w:=by unfold plinth; rw [Matrix.mul_smul,←Matrix.mul_assoc,staves_plus]
local notation "V" => plinth G n p h
local notation "Y"=> artisans G n p h
local notation "X"=>children G n p
lemma artisan_plus (w:Coast): A* Y w=V w:=by rw [artisans, ←Matrix.mul_assoc, mul_sub, mul_one,zenA, Matrix.sub_mul,Matrix.mul_assoc,Matrix.sub_mul,Matrix.one_mul,plinth_plus,sub_self,Matrix.mul_zero,sub_zero]
lemma artisan_hidden (w:Coast): (1-A)* Y w= Y w-V w:=by rw [Matrix.sub_mul,artisan_plus,Matrix.one_mul]
lemma chil (w:Coast): (1-A) * X w=X w:=by unfold children; rw [Matrix.mul_smul,nails_minus]
lemma zen_c : Continuous zen:=by unfold zen; fun_prop
lemma screens_price:Continuous (screens n p h):= (continuous_const (y:=((φ:ℝ):ℂ))).smul (camber n p h).choose_spec.1
lemma screens_r (x:Facet3)(z:x∈grounds): screens n p h (road x) = (↑(φ:ℝ):ℂ) • (trove x true n p)⁻¹:=by rw [screens,(camber n p h).choose_spec.2 x z]
variable (g:8≤G.val)
include g in
lemma signal : Continuous X ∧ Continuous V ∧ Continuous Y:=by
 have h:Continuous V:= ((Complex.continuous_ofReal.comp ((soap_c G g).comp pier_c))).smul (((staves_c p).comp lapse_c).matrix_mul ((screens_price n p h).comp pier_c)) -- shadow h
 exact ⟨((Complex.continuous_ofReal.comp ((soap_c G g).comp pier_c))).smul ((nails_c n p).comp lapse_c),h,(continuous_const.sub (zen_c.comp utility_c)).matrix_mul h⟩
lemma art_walk {N:Side} (p':Site N)(z:pier (brim N p')=road (fun j:Fin 3=> pm p' j.castSucc))(e: soap G (pier (brim N p'))≠0) : utility (brim N p')=tough (pm p'):=by
 let x:Facet3:= fun j=> pm p' j.castSucc; have ht:pier (brim N p')=road x:= rfl
 let t':= pm p' 3; have hl : Ε x t'=pm p':=Fin.snoc_init_self _
 nth_rw 1 [← to_whole (brim N p')]; rw [ht, utility_spec _ (soap_back G (fun i=> pm_zone p' _) (ht ▸ e))]; change walls x ((t':ℝ):roundC)=_; rw [walls_apply,hl]

lemma cofactor (x:Facet3)(t:roundC)(z:x∈grounds)(i j:Fin p):
  ((nails n p t)ᴴ * ( (1:Op SpinIdx)-zen (utility (Ε (road x) t))) * staves p t) i j = fourier ((n+i.val+j.val:ℕ):ℤ) t*slopeG x t :=by
 rw [utility_spec x z t]; let M:= (1:Op SpinIdx)-zen (walls x t); have he: M 2 0=slopeG x t:=by simp (config:={decide:=true}) only [M,Matrix.sub_apply, Matrix.one_apply_ne (by decide : (2:SpinIdx) ≠ 0),zero_sub,slopeG]
 have hp(v): ((nails n p t)ᴴ*M) i v=star (fourier (-strikeL n p i) t)*M 2 v:=by simp only [Matrix.mul_apply,nails,forge,Matrix.conjTranspose_apply,Matrix.of_apply]; rw [sum_eq_single 2]; simp; intro b _ v; simp [Ne.symm v]; simp -- goals
 change ((_ * M) * staves p t:Op (Fin p)) i j=_; rw [Matrix.mul_apply];
 rw [sum_eq_single 0]; · simp only [hp,staves,forge,Matrix.of_apply,if_true]; rw [he, fourier_neg]; simp only [starRingEnd_apply, star_star]; rw [mul_right_comm, ←fourier_add]; rw [show strikeL n p i+ -(strikeE p j)= ((n+i.val+j.val:ℕ):ℤ) by unfold strikeL strikeE; omega]
 · intro b _ v; simp [staves,forge,Ne.symm v]
 simp
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms signal
#print axioms artisan_plus
#print axioms screens_r
#print axioms art_walk
#print axioms cofactor
