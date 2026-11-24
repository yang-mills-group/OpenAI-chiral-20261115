import GaugeFieldConstruction.Peasant
set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One Lamp
open Lattice CF CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.XGarden.MastTin.ArtCart.Violets CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators Classical
open HopeC CF.Buffered CF.Buffered.Lifted
variable {N:Side}(t:ℕ→ℝ)(T:Tendsto t atTop (𝓝 0))(W:∀ᶠ i:ℕ in atTop,0<t i){a b d:ℕ→Payν N}{x y z:E4}
-- need fixed genres (apply each separately)
def Wagon {N:Side} (a:ℕ→Payν N)(P:Genre)(V:ℝ):Prop:=∀ i,(a i).2.1=P ∧ (a i).2.2 ∈ Glamor (Θk N (a i).1) P V
lemma couponL {P V} (Z: Wagon a P V)(w:300 < N.val): ∃ L:ℕ,∃ u>0,∀ i,Fintype.card (Eams (a i)) ≤ L ∧ ∀ j, ‖Forces (a i) j‖≤u:=by
 obtain ⟨L,u⟩:= SZbound N P; obtain ⟨C,c,Q⟩:= kiosk P V w; refine ⟨L,C,zero_lt_one.trans_le c,?_⟩; intro i; specialize Z i; revert Z; cases a i with | mk x b => cases b with | mk t b=> intro Z; obtain ⟨h,H⟩:= Z; change t=P at h; subst t; exact ⟨u x,Q x b H⟩ -- tune def Wagon
abbrev Mouth {N:Side}(a:Payν N)(t:ℝ): E4:= mount t a.1
abbrev Sails {N:Side}(t:ℕ→ℝ)(a:ℕ→Payν N)(x:E4): Prop:=Tendsto (fun i=> Mouth (a i) (t i)) atTop (𝓝 x)
lemma Stroll (u:Sails t a x)(v:Sails t b y): Tendsto (fun i=>NaR (t i) (a i).1 (b i).1) atTop (𝓝 (y-x)):= (v.sub u).congr (fun i=> by unfold Mouth NaR mount; rw [smul_sub])
variable (m:ℕ)
include T W
lemma crestB (u:Sails t a x)(v:Sails t b y)(g:x≠y): ∃ C≥1,∀ᶠ i:ℕ in atTop,Captain (t i) (a i).1 (b i).1 m C:=by
 let P:= Stroll t u v; let Q:=Stroll t v u
 obtain ⟨C,h,H⟩:=Gauken _ (fun i=>(a i).1) (fun i=>(b i).1) t T W P (sub_ne_zero.mpr g.symm) m; obtain ⟨D,p,V⟩:= Thröken _ (fun i=>(a i).1) (fun i=>(b i).1) t T W P (sub_ne_zero.mpr g.symm) m; obtain ⟨E,w,U⟩:=Thröken _ (fun i=>(b i).1) (fun i=>(a i).1) t T W Q (sub_ne_zero.mpr g) m; refine ⟨1+C+D+E,by linarith,?_⟩
 filter_upwards [H,U,V,W] with i H U V W; unfold NaR at H U V; rw [smul_sub] at H V U
 refine ⟨fun x y z t=>(H _ _ z t).mono (by linarith) (by positivity),fun x y z t=>(V _ _ z t).mono (by linarith) (by positivity),fun x y z t=>(U _ _ z t).mono (by linarith) (by positivity)⟩ -- tune def
abbrev Pearl2 (t:ℝ)(m:ℕ)(a b:Payν N)(C:ℝ):Prop:= Rally C (t^(m+1)) (quotaZ a b κg κF/((t:ℂ)^(pPow a+pPow b))) (BigP (Mouth a t) (Mouth b t) (RankBook t m a) (RankBook t m b))
abbrev Pearl3 (t:ℝ)(m:ℕ)(a b d:Payν N)(C:ℝ): Prop:= Rally C (t^(m+1)) (quotas a b d κg κF/((t:ℂ)^(pPow a+pPow b+pPow d))) (prism (Mouth a t) (Mouth b t) (Mouth d t) (RankBook t m a) (RankBook t m b) (RankBook t m d))
lemma Fount2 {P U V H}(k:300 < N.val)(p:Wagon a P U)(h: Wagon b V H)(A:Sails t a x)(B:Sails t b y)(l:x≠y): ∃ C≥0,∀ᶠ i:ℕ in atTop, Pearl2 (t i) m (a i) (b i) C:=by
 obtain ⟨L,Uc,Lp,Z⟩:= couponL p k; obtain ⟨M,Wc,hp,S⟩:=couponL h k; obtain ⟨C,Cp,G⟩:=crestB t T W m A B l
 refine ⟨↑L*(↑M*(Uc*Wc*cashF C)),by unfold cashF; positivity,?_⟩; filter_upwards [W,G] with i hi g; exact Ring2n _ hi m _ _ g Cp (Z i).1 (S i).1 (Z i).2 (S i).2 Lp.le hp.le
lemma Fount3 {P U V H G Y}(K:300<N.val)(p:Wagon a P U)(h:Wagon b V H)(w:Wagon d G Y)(v:P≠ .mixed)(A:Sails t a x)(B:Sails t b y)(C:Sails t d z)(l:x≠y)(L:y≠z)(Wk:x≠z): ∃ C≥0,∀ᶠ i:ℕ in atTop,Pearl3 (t i) m (a i) (b i) (d i) C:=by
 obtain ⟨R,U₁,h1,T1⟩:=couponL p K; obtain ⟨M,U₂,h2,T2⟩:=couponL h K; obtain ⟨J,U₃,h3,T3⟩:=couponL w K
 obtain ⟨E,e,e1⟩:=crestB t T W m A B l; obtain ⟨F,f,f1⟩:=crestB t T W m A C Wk; obtain ⟨S,s,s1⟩:=crestB t T W m B C L
 refine ⟨↑R*(↑M*(↑J*(U₁*U₂*U₃*cashF (E+F+S)))),by unfold cashF; positivity,?_⟩; filter_upwards [W,e1,f1,s1] with i hi a b c
 exact Ring3n _ hi m _ _ _ (by rw [(p i).1]; exact v) (extraK _ _ _ _ hi.le a (show E ≤ E+F+S by linarith)) (extraK _ _ _ _ hi.le c (by linarith)) (extraK _ _ _ _ hi.le b (by linarith)) (by linarith) (T1 i).1 (T2 i).1 (T3 i).1 (T1 i).2 (T2 i).2 (T3 i).2 h1.le h2.le h3.le
#print axioms Fount3
end YM.GaugeFieldConstruction.Wick.Yacht
end
