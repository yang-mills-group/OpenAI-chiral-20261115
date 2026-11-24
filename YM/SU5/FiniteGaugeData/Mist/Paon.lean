import YM.SU5.FiniteGaugeData.Mist.Leda
/-! # Abstract estimate for genuine unprojected paths only needing ONE layout and chronology.-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Mist.Leda
open Function Filter Metric Finset Lattice Hills Hike
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal
variable {H:Hilbert}{L:Side}{a:Axis}{σ:Type}(P:Terrace H L a)
variable (S:OS.Semigroup H a)(d:σ→ℝ)(Ω:H.space)(z:ℝ)
local notation "R"=> VistaQ L
variable (A B:Grid σ (VistaQ L))(J:List σ)
-- Pay continuity along relative shifts gear.TH
private abbrev Lag (x:Carousel L)(k:ℝ) := S.E ((↑(x a)-k).toNNReal) * spireT P x -- coe.B
abbrev giro (i j:σ) : H.Op := S.E ((↑(A j a)-↑(A i a)-d i).toNNReal) * spireT P (A j-A i)
lemma giro_sync (i j:σ) : giro P S d A i j=Lag P S (A j-A i) (d i):= rfl
lemma giro_rel (i j:σ)(p:A j-A i=B j-B i): giro P S d A i j=giro P S d B i j:=congrArg (fun x=> Lag P S x (d i)) p
variable [DecidableEq σ]
lemma mixed (w:R)(i:σ)(b:Axis)(p:a≠b): Hike.aerate A J a w i b=A i b:=by by_cases t:i∈J <;> simp [aerate,t,p,Ne.symm p]
lemma mGait (i j:σ)(c:R→H.space)(p:Continuous c): Continuous fun t=> giro P S d (Hike.aerate A J a t) i j (c t):=by
 let f(k:σ)(t:R):=((aerate A J a t k a):ℝ); have h(k:σ):Continuous (f k):= ((continuous_subtype_val.comp (continuous_apply a)).comp (continuous_apply k)).comp (aerate_C ..)
 let G t:= ((f j t-f i t-d i).toNNReal); have he:Continuous G:= continuous_real_toNNReal.comp (((h j).sub (h i)).sub continuous_const)
 let Q(t:R):=spireT P (aerate A J a t j-aerate A J a t i); have hz:∀ t,Q t=Q 0:=fun t=> glide_self P _ _ (fun b p=> by simp only [Pi.sub_apply,mixed A J _ j b p.symm,mixed A J _ i b p.symm])
 let v(t:R):=Q t (c t); have hv:Continuous v:= (show v= fun t=>Q 0 (c t) from (funext fun i=> DFunLike.congr_fun (hz i) (c i))) ▸ (Q 0).continuous.comp p
 exact steamV S v G he hv -- order
lemma money_promo (F:σ→ H.Op)(Z:List σ): Tendsto (fun t:VistaQ L=>usual Ω F (giro P S d) Z (aerate A J a t)) (𝓝 0) (𝓝 (usual Ω F (giro P S d) Z A)):=by
 let f(t:R):= TapeT F (giro P S d (aerate A J a t)) Z Ω; have ht:Continuous f:= payT F _ (mGait P S d A J) Ω Z; have h:Continuous fun t=> inner ℂ Ω (f t):= (innerSL ℂ Ω).continuous.comp ht
 convert (h.tendsto 0); rw [aerate_home]
private lemma pocket (S V K T:H.Op)(h:Commute S T)(p:V=T*K):S*V=T*(S*K):=by rw [p,←mul_assoc,h.eq,mul_assoc]
lemma kettle_p (h:∀ v:VistaQ L,∀ b:Axis,∀ w:ℝ≥0,Commute (S.E w) (ramble P b v))(i j:σ)(b:Axis)(w:VistaQ L)(g:b≠a)(t:B j-B i=A j - A i + Pi.single b w) : giro P S d B i j= ramble P b w * giro P S d A i j:=by
 rw [giro_sync,giro_sync,t]; unfold Lag; let V:= A j - A i; have hg : (A j-A i+Pi.single b w:Axis→VistaQ L) a= (A j-A i) a :=by simp [Ne.symm g]
 rw [hg]
 apply pocket _ _ _ _ (h ..); exact (glide_more P Terrace.scheduleL (A j-A i) (Pi.single b w)).trans (Eq.trans (congrArg (fun x:H.Op=> spireT P (A j-A i)*x) (glide_one P _ _)) ((glide_group P Terrace.scheduleL (A j-A i) (ramble P b w) (fun v _=> ramble_across P b v _ _)).eq).symm)
end YM.CF.Buffered.Afterglow.Hierarchy.Mist.Leda
