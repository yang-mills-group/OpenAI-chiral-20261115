import YM.CF.BProof.Law.Replay
import YM.CF.BProof.Angular.Avenue
import YM.CF.BProof.Angular.Relative

/-! Fixed collar copying surfaces and stage extension price. These True-field properties
will be used even after computing every severe check in a band/gap pair. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular.Yard
open Function Filter RG Wilson Lattice Finset Work MeasureTheory CF.BProof.Face Mag Law
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {s:Side}(Y:Yard s)(y:ℝ)(S: Hall s)(U:Config G s)(F:Y.FaceS)

def Climbed : Prop:=∀ i,¬ Y.D i → lifts (Y.u i) Y.long y S U (F i)
def Firmly(i:Y.Index)(g: Bool):= ∃ r m,Firm S.K (outlook (Y.u i) Y.long S U (F i) g) r m
lemma firm_ok {X:Design}{K: Chart G}{v:ℝ}(hv:0<v) : ∀ᶠ y:ℝ in atTop, ∀ {s:Side}(Y:Yard s)(S:Hall s)(U:Config G s)(F:Y.FaceS), S.X=X→ S.K=K→ Sized v S.g y S.k→ X.k₀ ≤ S.k →
    Y.Climbed y S U F → ∀ i,¬Y.D i→ ∀ b:Bool,Y.Firmly S U F i b:=by
 obtain ⟨C,hc,H⟩:= firm_read X K v hv; filter_upwards [H] with y H
 intro s Y S U F ht hk u p H' i hi b; refine ⟨_,_,show Firm S.K _ (blendR X K S.g) (C*mA y) from ?_⟩; replace H':= H' i hi b; unfold outlook sight; rw [ht,hk]; rw [hk] at H'; exact (H S.g S.k u p (inlet (Y.u i) _ U b) (F i b) H').1

/-- This predicate suffices for all D-side estimates and copies, not conditional gauge. -/
structure Climate : Prop where
  flat : Y.Flat U
  awake (i:Y.Index)(a:Bond s) : a∈Y.leases i → cd G (Y.slot i y S U F a) (U a) ≤ xi y
  firm (i:Y.Index) : ¬ Y.D i → ∀ b:Bool,Y.Firmly S U F i b
lemma verses (A:Config G s)(h:Set.EqOn A U ↑Y.field){i:Y.Index}(d:¬Y.D i): Firmly Y S A F i=Firmly Y S U F i:=by
 ext b; unfold Firmly outlook sight; rw [sweeps_eq Y i A h d b]
lemma created (A:Config G s)(h:∀ i,¬Y.D i→∀ b,Y.Firmly S U F i b) (u:∀ i:Bond s,SU.group.chord (A i)≤xi y): Climate Y y S (Y.play y S U F A) F:= by
 let V:=Y.play y S U F A; have hp:Set.EqOn V U ↑Y.field:= Y.mix_field ..; refine ⟨Y.squash_flat _,fun i q hq=> ?_,fun i g b=> ?_⟩
 · change cd G (Y.slot i y S V F q) (Y.play y S U F A q)≤_; rw [played Y y S U A F i hq]; have he: Y.slot i y S V F q=Y.slot i y S U F q:=by
     unfold slot; split; rfl; next H=> rw [Y.baseN_eq i S V F U hp H]
   rw [he]; nth_rw 1 [← mul_one (Y.slot i y S U F q)]; rw [cd_mul_left,cd_one]; exact u q
 change Y.Firmly S V F i b; rw [Y.verses S U F V hp g]; exact h i g b
lemma climbed (p:Y.Glyph)(h:accepted Y y S U p) : Climbed Y y S U (sweepLabel Y y S U p):=by
 intro i g; unfold sweepLabel; rw [if_neg g]; specialize h i; rw [if_neg g] at h; exact (wages_mem ..).1 h
lemma haven (h:Y.Climate y S U F)(i:Y.Index)(d:Y.D i)(u:Bond s)(v:Wet (Y.u i) Y.long u) : cd G (mag y u) (U u)≤ xi y:=by
 have hp:= h.awake i u (show u∈ Y.leases i from by rw [leases,if_pos d,mem_wash]; exact v); rwa [slot,if_pos d] at hp
lemma cushion {i:Y.Index}(x:Per s)(b:Bool) (hf:Y.Firmly S U F i b)(hq:flag (Y.u i) x Y.long=b) (h: angle Y.long (along (Y.u i) x) = if b then 1 else 0): sheet (Y.baseN i S U F) x=inlet (Y.u i) Y.long U b:=by
 let a:=Y.u i; let l:=Y.long; let V:=sight a l S U (F i); let W:=formal a l S U (F i); have hv: ∀ p:Space s, Y.high i S U F (join x p)= V b p:=by intro p; simp only [high,space_join,time_join,hq,a]; exact rfl
 have he : sheet W x=react (V b) (inlet a l U b):= by
   funext p; unfold sheet W; rw [horizontal_light]; unfold light profile; change link _ (angle Y.long (along (Y.u i) x)) _ _= outlook a l S U (F i) b _; rw [h]; obtain ⟨k,q,g⟩:=hf; cases b; exact link_a S.K _ _ (g.pay _); exact link_b S.K _ _ (g.pay _)
 unfold baseN; rw [sheet_gauge]; simp_rw [Pi.inv_apply,hv]; rw [show sheet _ x=react (V b) (inlet a l U b) from he]; exact react_inv ..
lemma cold_flag {r} (i:Y.Index)(x:Per s)(hr:4*r<Y.long) (h:Y.Cold i r x): flag (Y.u i) x Y.long=true ∧ angle Y.long (along (Y.u i) x)=1:=by
 have hp:=Y.before_u i h.2; have hx:= h.1; exact ⟨(flag_true ..).mpr (by unfold cut; omega), angle_one _ Y.long_pos (by omega)⟩
lemma hot_flag {r} (i:Y.Index)(x:Per s)(hr:4*r<Y.long)(h:Y.Hot i r x): flag (Y.u i) x Y.long=false ∧ angle Y.long (along (Y.u i) x)=0:=by
 have hp:=h.1; exact ⟨(flag_false ..).mpr (by unfold cut; omega), angle_zero _ Y.long_pos (by omega)⟩
lemma copy (h:Y.Climate y S U F) (x:Per s)(i:Y.Index)(hx:Y.Band i x)(d:¬Y.D i)
    (b:Bool)(hq:flag (Y.u i) x Y.long=b) (ht: angle Y.long (along (Y.u i) x) = if b then 1 else 0)(j:Slat s) : cd G (inlet (Y.u i) Y.long U b j) (sheet U x j)≤xi y:=by
 let l:=Y.long; let a:=Y.u i; set v:=along a x; by_cases k: 0<v∧ v<l
 · rcases j with ⟨p,n⟩; have he:= h.awake i (horiz x p n) (by rw [leases,if_neg d, watch_h]; exact k)
   rw [slot,if_neg d] at he; rw [← cushion Y S U F x b (h.firm i d b) hq ht]; exact he
 have hp:x=front a l b:=by
    unfold Band at hx; change v≤l at hx; have ht:x=a+v:=(add_along a x).symm
    by_cases hv:v=0
    · have hx: x=front a l false:=by rw [front_left]; simpa only [hv,Nat.cast_zero,add_zero] using ht
      have hv: b=false:= by rw [← hq,hx]; exact onside a l _ Y.long_pos (Y.long_lt.trans Y.count_lt) -- tune dots
      rw [hv]; exact hx
    have hx:x=front a l true:=by rw [front_right]; rw [show v=l by omega] at ht; exact ht
    have hv: b=true:=by rw [←hq,hx]; exact onside a l _ Y.long_pos (Y.long_lt.trans Y.count_lt)
    rw [hv]; exact hx
 rw [hp]; change cd G (inlet a l U b j) (inlet a l U b j)≤ _; rw [cd_self]; exact (coin_pos ..).le
end YM.CF.BProof.Angular.Yard
