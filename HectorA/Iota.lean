import HectorA.InShift
set_option autoImplicit false
noncomputable section
namespace Yoland
open YM Filter Set Function
open YM.OS YM.OS.Semigroup
open scoped Topology NNReal InnerProductSpace BigOperators Classical
variable {H:Hilbert}{j:Axis}(S:OS.Semigroup H j)(x:H)
attribute [local instance] InnerProductSpace.complexToReal
abbrev stable(k:H)(U:H.Op):Prop:=U k=k
lemma keeps(i:ℕ){p:ℝ}(q:0<p)(t:∀r,dawn S r x=x)(h:0 < i): pay S i p x=0:=by rw [← paid S x q,detail,show tempo S x=(fun _=>x) from funext t]; rw [iteratedDeriv_const,if_neg h.ne']
lemma turnΩ (R:H.Op)(h:∀t y,R (S.E t y)=S.E t (R y))(k:ℕ){t:ℝ}(e:0<t): R (pay S k t x)=pay S k t (R x):=by
 rw [←paid S _ e,←paid S _ e]; unfold detail
 let L:= R.restrictScalars ℝ
 have hv:= transport (((civilB S x).price t) e) L k
 rw [← show L (iteratedDeriv k (tempo S x) t)=R (iteratedDeriv k (tempo S x) t) from rfl,←hv]
 exact congrArg (fun f:ℝ→(H).space=> iteratedDeriv k f t) (funext fun y=>h _ _)
lemma growJet(i:ℕ){a t:ℝ}(h:0<t)(p:0<a): pay S i a (dawn S t x)=pay S i (a+t) x:=by
 have he:=earns_asset S 0 i t a h p
 rw [show pay S 0 t=dawn S t from congrFun iteratedDeriv_zero t,natAdd, add_comm t a] at he
 exact DFunLike.congr_fun he x
where natAdd(i:ℕ):i+0=i:=rfl
-- CLM-app continuity
lemma cloverLift {f:ℕ→H.Op}{F:H.Op}{g:ℕ→H}{x:H}(h:Tendsto f atTop (𝓝 F))(u:Tendsto g atTop (𝓝 x)): Tendsto (fun d=>(f d) (g d)) atTop (𝓝 (F x)):= (show Continuous (fun z:H.Op × H => z.1 z.2) from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (h.prodMk_nhds u)
#print axioms keeps
#print axioms growJet
end Yoland
