import YM.CF.BProof.Trek.Home
import YM.CF.BProof.Angular.Tape
/-! Compile Scriptures for choices facing true Mark estimator. Supplies tested after Axial.
For use before flattening keep local versions `winter`,`summer`. Work for any eyes if off domains. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset Hearth
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c c':Side} (Y:Yard s)(i:Y.Index)(S:Hall s)(f:Ratio c s)(U:Bkg s)(b:Eyes s)
-- scatter signs indexed by right gap.
def planeN (q:Y.Glyph) (i:Y.Index) (x:Space s) := if Y.D i then q (i+1) (false,x) else q i (true,x)
lemma planeν {i:Y.Index}{r:Bool}(h:¬Y.D i)(q:Y.Glyph) (x:Space s): planeN Y q (Y.location i r) x=q i (r,x):=by cases r <;> simp [planeN,Yard.location, Y.prev,h]
lemma sideN (i:Y.Index): ∃ j:Y.Index, ∃ t:Bool, ¬ Y.D j ∧ i= Y.location j t := by by_cases h:Y.D i; exact ⟨i+1,false,fun x=>(Y.next i).1 x h,by simp [Yard.location]⟩; exact ⟨i,true,h,rfl⟩
def winter (x:Site s) := if Y.D i then apex else XN (Y.u i) Y.long S f U b x
def summer (x: Site s) := if Y.D i then BM 1 else HN (Y.u i) Y.long S f U b x
def actual (Y:Yard s)(b:Y.FaceS)(L:Y.Glyph) : Script Y where
 X i:= winter Y i S f U (b i)
 K i:= summer Y i S f U (b i)
 frame i := (gown (Y.u i) Y.long U (b i))⁻¹
 label:= planeN Y L
lemma coinN {i:Y.Index}(t:¬Y.D i)(x:Site s)(b:Y.FaceS)(L:Y.Glyph)(p:x∈ Y.band i) : (actual S f U Y b L).code x=L i (flag (Y.u i) (time x) Y.long, BProof.space x):=by unfold Script.code; rw [code_tag ..]; exact planeν Y t L _; exact p
lemma wear(g:Site s→E)(u:¬Y.D i)(x:Site s): winter Y i S f (gauge g U) (b*(eye (Y.u i) Y.long g)⁻¹) x = scaledV (g x) (winter Y i S f U b x) ∧ summer Y i S f (gauge g U) (b*(eye (Y.u i) Y.long g)⁻¹) x=motion (g x) ∘ summer Y i S f U b x:=by
 simp_rw [winter,summer,if_neg u,XN_bead,HN_bead]; simp
lemma strong (V:Bkg s)(h: Agrees (↑(Y.band i)) U V)(q:4≤c.val)(e: Width f Y.long)(x:Site s)(t:x∈Y.band i): winter Y i S f U b x=winter Y i S f V b x ∧ summer Y i S f U b x=summer Y i S f V b x:=by unfold winter summer; split; exact ⟨rfl,rfl⟩; exact ⟨XN_here (Y.u i) Y.long S f U b V (wide Y) e q h t,HN_here (Y.u i) Y.long S f U b V (wide Y) e q h t⟩
lemma nightsM(x:Site s) : Money (summer Y i S f U b x) ∧ summer Y i S f U b x 0=Pair.fullM (winter Y i S f U b x).val:=by unfold winter summer; split; exact ⟨moneyB z1,BM_x ..⟩; exact ⟨HN_money ..,HN_first ..⟩
lemma storyL (x:ℝ): Measurable (fun p:Street s=>fun t=> summer Y i S f p.1 p.2 t x):=by apply measurable_pi_lambda; intro t; unfold summer; split_ifs; exact measurable_const; exact (measurable_pi_apply (X:=fun _:Site s=>Stamp) t).comp (HN_m ..)
lemma tideL : Measurable (uncurry (winter Y i S f)):=by apply measurable_pi_lambda; intro t; unfold winter uncurry; dsimp only; split_ifs; exact measurable_const; exact (measurable_pi_apply (X:=fun _:Site s=>Ballot) t).comp (XN_m ..)
section token
variable (G:Y.FaceS)(L:Y.Glyph)(B:Blocks Y c')(g:Ratio c' s){u v:ℝ}(H:Herald u v){t:ℕ}(C:Sized t H.whole){y r m d:ℝ}
local notation "D"=> actual S f U Y G L
structure Light (S:Hall s) (f:Ratio c s)(y r m d:ℝ):Prop where
 warm : H.Warm Y.long y  -- namespace notation adjust
 p : ∀ i,¬Y.D i→ Facing (Y.u i) Y.long S U (G i) f y r m
 heat(i:Y.Index)(h:Y.D i): Ground d U ↑(Y.band i)
 camp (i: Y.Index)(b: Bool)(h:¬Y.D i)(x:Space s)(g':ClearB Y g B (Y.location i b) x 2): cd group (G i b x) (Mag.center (L i (b,x))) ≤ d
 lens (i:Y.Index)(b:Bool)(h:¬Y.D i)(x:Space s)(n:TAxis)(v':ClearB Y g B (Y.location i b) x 2)(h': ClearB Y g B (Y.location i b) (x+tstep n) 2) : L i (b,x)= L i (b,x+tstep n)
 near (b:Bond s)(h:Y.Vic (tag Y b.1) C.blockY (time b.1))(p:distant Y g B b.1 2): group.chord (U b)≤d
 already : Y.Flat U
-- generative
lemma grantN (p:f.count=H.body)(w:4≤ c.val)(z:Sound Y H C d)(q:Light Y U G L B g H C S f y r m d): Permit D C U g B d:=by
 let W:=Herald.Warm.length q.warm; have hw:Width f Y.long:=by rw [Width,p]; exact W
 have he(i:Y.Index)(v:¬Y.D i):= H.ticketN (Y.u i) Y.long S f U (G i) y p (wide Y) w q.warm (q.p i v)
 refine ⟨fun i x _=>(nightsM Y i _ _ _ _ x).1,fun i x _=>(nightsM Y i _ _ _ _ x).2,fun i=>?_,fun i t p'=>?_,fun i h x _=> ⟨if_pos h,if_pos h⟩,fun i h x u v=>?_,fun i h x hx v t'=>?_,fun i x k e v=>?_, q.near⟩
 · change PaceX _ U (winter Y i S f U (G i)) _; unfold winter; split_ifs; rename_i ht; apply formsD_X U _ _ _ (q.heat _ ht); exact (by nlinarith [z.SX,z.fields,xm_p, div_pos rate_p (show 0<(Y.short:ℝ) from Nat.cast_pos.mpr Y.short_pos)]); rename_i ht; exact pace_sub _ _ (he i ht).2.1 (Set.Subset.refl _) H.gold_le -- tune
 · change SkinH _ _ (fun x=>summer Y i _ _ _ (G i) x t) v; simp only [summer]; split_ifs with v'; refine formsD_H U _ _ _ _ (q.heat i v') (by nlinarith [z.LH,z.fields,xm_p,div_pos rate_p (show 0<(Y.short:ℝ) from Nat.cast_pos.mpr Y.short_pos)]); exact (he i v').2.2 t p'
 · change winter Y i _ _ _ (G i) x=_∧summer Y i _ _ _ (G i) x=_; rw [winter,if_neg h,XN_rim, summer,if_neg h,HN_close _ _ _ _ _ _ hw v u]; exact ⟨rfl,rfl⟩; exact ⟨u,by unfold life; omega⟩
 · let b':=flag (Y.u i) (time x) Y.long; have hh: gown (Y.u i) Y.long U (G i) x= G i b' (BProof.space x):=by
      rw [gown,stage_layers, stage_identity (Y.u i) Y.long U (Y.long_lt.trans Y.count_lt) (fun x p u e=> q.already (Y.trunk_b p h u e)) hx, Pi.one_apply,mul_one]
   rw [coinN _ _ _ _ h x _ _ hx]; change cd group (gown (Y.u i) Y.long U (G i) x)⁻¹ _ ≤_; rw [hh, locus,cd_inv] -- inverse mistake center not inverse of goal (center vs label): comparing to `locus` so need cd_inv forward
   unfold distant at t'; rw [code_tag ..] at t'; exact q.camp i b' h _ t'; exact hx
 obtain ⟨j,b,h,rfl⟩:=sideN Y i; exact (planeν Y h L x).trans ((q.lens _ b h x k e v).trans (planeν Y h L _).symm) -- tune dependent Lean
end token
end YM.CF.BProof.Trek
