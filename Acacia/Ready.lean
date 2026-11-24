import Acacia.Amen
import HectorA.InShift
import Acacia.Rill
import Acacia.Smith
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace Acacia
open Filter Function Finset Set YM.OS YM Yoland
open scoped Topology NNReal BigOperators Classical InnerProductSpace
attribute [local instance] InnerProductSpace.complexToReal
lemma lobeR {H:Hilbert}{i:Axis}(S:OS.Semigroup H i)(d:ℝ)(p:0<d)(n:ℕ)(q:ℕ→ℝ)(h:∀s,0<q s)(v:Tendsto q atTop (𝓝 0)): Tendsto (fun s:ℕ=> Yoland.frame S n (q s) (dawn S d)) atTop (𝓝 (Yoland.pay S n d)):=by
 let e:=d/((n:ℝ)+1); have he:0<e:=by unfold e; positivity
 obtain ⟨A,m,l⟩:=way S h e he v d n (show (n:ℝ)*e ≤ d from (by
    unfold e; have hv:0<(n:ℝ)+1:= by positivity
    rw [←mul_div_assoc, div_le_iff₀ hv]; nlinarith))
 rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (g:=fun s=>q s*A) ?_ (by simpa using v.mul_const A)
 exact l.mono fun j t=> (delta_cpuS S n _ d (h j).le p.le) ▸ t
#print axioms lobeR
end Acacia
