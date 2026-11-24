import YM.SU5.Relativistic.MountainPath
import YM.CF.Lattice.Reference
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore Cuest Fock Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
local notation "Φ"=> Set.Icc (-π) π
attribute [local instance] screen_fin

-- probe amplitude. zen(heat) column. time-pulse registered minus. charge variety. confirm signs.
abbrev fell (i:SpinIdx)(k:Behind)(t:ℝ):ℂ:= -(zen (heatLine k t) i 0)
lemma fell_upper {i:SpinIdx}(h:i∈ Lat.plusHalf) (k:Behind)(t:ℝ): fell i k t=0:=by
 let C:= zen (heatLine k t); have hp:=Matrix.ext_iff.mpr (zenA (heatLine k t)) i 0; change (Aop*C) i 0=(C*(1-Aop)) i 0 at hp; rw [Adef, ← Lat.raising, ← dim_cut,cutM,cutM, Matrix.diagonal_mul,Matrix.mul_diagonal, if_pos h,one_mul,if_neg (by decide),mul_zero] at hp -- cut lemma ordering
 exact neg_eq_zero.mpr hp
lemma face_value (k:Behind)(t:ℝ):fell 2 k t= faceR k t:=by
 unfold fell faceR zen; simp only [Matrix.sum_apply, Axis,Fin.sum_univ_succ,Matrix.smul_apply, smul_eq_mul]
 change -((heatLine k t 0)*(I*0)+((heatLine k t 1)*(I*0)+(heatLine k t 2 * (I*I)+(heatLine k t 3*(I*1)+0))))=_; rw [Complex.I_mul_I]; change _ = heatLine k t 2-I*heatLine k t 3; ring
-- market.cont issue local
abbrev backPane := Set.pi (Set.univ : Set (Fin 3)) (fun _=>Set.Icc (-π) π)
structure UpStart (d:ℕ)(s:Finset ℤ)(c:ℤ→Behind→ℂ)(r a:ℝ):Prop where
 wage :0<r
 tail : r+dropH d+dropH d<π
 outside(k)(p:k∉interior (launch d r))(i:ℤ): c i k=0
 cont(i): Continuous (c i)
 beats(k:Behind): let g:=fun t=>∑ i∈s,c i k*soundT i t
                  wrapT 0 (fun t=>g t * fell 2 k t)=stationed d r k
 expense(i:Axis): TollS a (launch d r) (fun k n=>pluse n (fun t=>(∑ j∈s,c j k * soundT j t)* heatLine k t i))
theorem houses(a:ℝ)(p:0<a)(d:ℕ)(w:9≤d)(Q:ℤ) : ∃ (s:Finset ℤ)(c:ℤ → Behind→ℂ)(r:ℝ), (∀ i∈s,Q ≤ i) ∧ UpStart d s c r a:=by
 obtain ⟨r,e,t⟩:= launched d w; have ht:= launch_compact d r; have hz:= launch_sun e t; obtain ⟨s,c,h,k,v,x⟩:= sponsorSignal ht hz p Q _ (stationed_c d r); let U:= launch d r
 let p₀ : 0<d:=by omega
 have hp(i): ∀ z∉interior U,c i z=0:=fun z w=>x i z (stationed_off p₀ r z (fun g=>w (upland_interior d r g)))
 refine ⟨s,c,r,h,e,t,(fun k g i=> hp i k g),fun i=> continue_g ht _ (k i) (hp i),fun a=> ?_,v.2⟩
 intro m; by_cases hh:a∈ U
 · simp_rw [face_value]; exact v.1 a hh
 have he(i):c i a=0:= hp i a (fun g=>hh (interior_subset g))
 unfold m; simp_rw [he]; simp [wrapT,pluse,stationed_off p₀ r a (fun g=> hh (interior_subset (upland_interior d r g)))]

variable {d:ℕ}{s:Finset ℤ}{c:ℤ→Behind→ℂ}{a r:ℝ}
namespace UpStart
variable (P:UpStart d s c r a)
-- Fourier data. across ANY k.
def pledge (s:Finset ℤ)(c:ℤ→Behind→ℂ)(k:Behind)(t:ℝ):ℂ:= ∑ i∈s,c i k* soundT i t
def target (s:Finset ℤ)(c:ℤ→Behind→ℂ)(k:Behind)(t:ℝ): Ket SpinIdx:= pledge s c k t • acts (1-zen (heatLine k t)) (basisKet (0:SpinIdx))
def turned (s: Finset ℤ)(c:ℤ→Behind→ℂ)(i:SpinIdx)(k:Behind)(t:ℝ):= (target s c k t).ofLp i
local notation "Ω"=>target s c
local notation "Z"=>turned s c
local notation "U"=>launch d r
lemma tariffed (i:SpinIdx)(k:Behind)(t:ℝ): Z i k t = pledge s c k t * ((if i=0 then 1 else 0)+fell i k t):=by
 unfold turned target; simp only [WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul,basis_act, Matrix.sub_apply,Matrix.one_apply]; rfl
include P
lemma pledged (k:Behind)(p:k∉interior (launch d r))(t:ℝ):pledge s c k t=0:=by unfold pledge; simp [P.outside k p]
lemma elsewhere (k: Behind)(p:k∉interior (launch d r))(t:ℝ): Ω k t=0:=by unfold target; rw [P.pledged _ p,zero_smul]
lemma pledge_c : Continuous (uncurry (pledge s c)):= continuous_finsetSum _ fun j _=> ((P.cont j).comp continuous_fst).mul ((sound_con j).comp continuous_snd)
local notation "κ"=>Set.univ ×ˢ Set.Icc (-π) π
lemma turned_c(i:SpinIdx):ContinuousOn (uncurry (Z i)) κ:=by
 have hp : ContinuousOn (fun p:Behind×ℝ=> fell i p.1 p.2) (U ×ˢ Set.Icc (-π) π):=by
    unfold fell zen; simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]; exact (continuousOn_finsetSum _ (fun j _=> (heat_cont (launch_compact ..) (launch_sun P.wage P.tail) j).mul continuousOn_const)).neg
 apply continue_k (launch_compact d r)
 · change ContinuousOn (fun p:Behind × ℝ => turned s c i p.1 p.2) _; simp_rw [tariffed]; exact (P.pledge_c.continuousOn.mono (subset_univ _)).mul (continuousOn_const.add hp)
 intro i p; unfold uncurry; rw [tariffed,P.pledged i.1 p,zero_mul] -- syntax
omit P
lemma homeEnd (i:SpinIdx)(k: Behind):Eq (Z i k (-π)) (Z i k π):=by
 rw [tariffed,tariffed]; unfold pledge fell; simp_rw [agree_s,funext (agree_seam k)]; -- tune
where agree_s (j:ℤ):soundT j (-π)=soundT j π:=by unfold soundT; rw [←Int.cast_neg]; have hz:=wrap_surge (-j) 1 (-π); rw [show -π+φ*(↑(1:ℤ):ℝ)=π from (by push_cast; ring)] at hz; exact hz.symm
end UpStart
end YM.CF.Crest.Sleet
