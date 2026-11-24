import YM.SU5.FiniteGaugeData.Brique.Tiler
import YM.SU5.FiniteGaugeData.Steam.Repetition
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique
section
variable {m B L:Side}{u n j w h l i k K:ℕ} {e d:ℝ}
private def Flock (p : Peg m)(S:Support (More m))(F:Mark m)(i h:ℕ)(e d:ℝ):=∃ a b:ℕ, a+b=i ∧ b ≤ a ∧ Crater h e d p S F a false ∧ Crater h e d p S F b true
private lemma flock_powers{p:Peg m} (P:Margin L w l K u){S T:Support (More m)}{F G: Mark m}(B':Mirror B u m S F T G n)(q: Flock p S F i h e d)(g:AtSupport false S F):Flock p T G (i*n) h e d:=by
 induction B' generalizing i with
 | self=> rwa [mul_one]
 | @grow S F a z t=>
   obtain ⟨x,y,v₀,gd,A,V⟩:= q; let s:= gaugeShift B z; let T:=S.image ((plane a s).anon m); have J:Disjoint T S:= by
    refine Finset.disjoint_left.mpr ?_; intro y e f; have he:= margin_separate a s P y y (Finset.image_subset_image (f:=(plane a s).anon m) t e) (t f); simp at he
   exact ⟨y+x,x+y,by omega,by omega,(V.reflects a s).merger (g.refl ..) A g J,(A.reflects a s).merger (g.refl ..) V g J⟩
 | trans B C ih it=> rw [←mul_assoc]; exact it (ih q g) (B.covers g)
lemma Mirror.bullet{p:Peg m} (P:Margin L w l K u){S T:Support (More m)}{F G: Mark m}(B':Mirror B u m S F T G n)(p₁:0≤d)(q:Crater h e d p S F i false)(g:AtSupport false S F):∃ a:ℕ, i*n≤2*a ∧ Crater h e d p T G a false:=by obtain ⟨a,b,v,w,A,-⟩:= flock_powers (i:=i) P B' ⟨i,0,by omega,by omega,q,Crater.trivial p₁ F⟩ g; exact ⟨a,by omega,A⟩
end
open Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
set_option quotPrecheck false
variable (s i k:ℕ)
local notation "Σ" => ((Y.voyage i).X (Y.uv k))
local notation "Ω" => side Y i s
local notation "V" => (storeH Λ.V)
local notation "A" => ((Y.voyage i).X (Y.uv k)).gram s
local notation "Q" => (Y.voyage i).CapeT s
local notation "WT" => hat Λ.R.L Λ.x s
-- eligibility threshold is on period. counts rounding tilt angular `grasp.roundZ≤` carried always. 
def Master (s i : ℕ): Prop:= Travels Λ ∧ (storeH Λ.V).n ≤ (side Y i s).val
variable (D:Master Y s i)
lemma side_grows (h:Real.exp 1 ≤ Λ.x) (p:StrictMono u)(x:ℕ): ∀ᶠ i:ℕ in atTop,x ≤ (side Y (u i) s).val:=by
 filter_upwards [((c_grows (tent Y h)).comp ((momentum Y s).comp p.tendsto_atTop))|>.eventually_ge_atTop x] with i d; rw [show side Y (u i) s= _ from (terrain Y h (Y.ir (u i)) s).symm]; exact d
lemma masters (h:Real.exp 1 ≤ Λ.x) (p:StrictMono u)(x:Travels Λ):∀ᶠ i:ℕ in atTop,Master Y s (u i):=(side_grows Y s h p _).mono fun _ p=>⟨x,p⟩
variable {α C ε:ℝ} (B':Club Y g s)
variable (p:s≤ Y.uv k)
include p in
lemma credit_full: Hom.InterestX Λ.W.C (side Y i s) (A).J:=by
 let X:= Σ
 let U: Py.Period.Session Λ.V 1 2 6 Λ.N0 Λ.J Chi.canonical Λ.h Λ.R0 Λ.δ Λ.x (Y.ir i) (Y.uv k):= ⟨Y.meter,(Y.voyage i).funds,X.pilot,X.gram,(Y.voyage i).CapeT,X.wave,X.fee,Y.history i k⟩
 exact Period.credit_rule Λ.V 1 2 6 Λ.N0 Λ.J _ _ _ _ U s p
lemma enough_y : Λ.U.roundZ ≤ (side Y i s).val:= Λ.J.gran.trans ((Y.voyage i).ownership s).size
include D p
lemma posters (w:ℕ): Life Λ.K.j (A).J Λ.d (V).C w (tailCost (V).c (V).C w) :=by
 let hk:= credit_full Y s i k p; let T:= Brush Λ.V _ hk -- missing arg?
 let P:= (storeH Λ.V).posse.tanker _ D.2 T _ D.1; refine ⟨bracewell (enough_y ..) Λ.V.note (by rw [Λ.kJ]; decide) T,ambient_value P, casing_neighbor P w⟩ -- tune
omit D p
lemma posters_p : Roof (side Y i s) Λ.J.k Λ.d Λ.J.n ((Y.voyage i).CapeT s) := let T:= ((Y.voyage i).ownership s).paid; {T with paid:=fun i=>(T.paid i).shrink Λ.J.hr.le}
local notation "ζ" => slopeF Λ.W g
-- estimated exponent per whole gauge site (More, sum bill). Plenty slack even without More, but unify with denominator in steam.
-- Discovery price may need this at staged Story cutoff h. parameterize independently via calling V + G; in WP lower. don't include Λ.x.
def zen (g C:ℝ):= g+180*C -- ζ here = budget per vol
lemma zen_pos (x y:ℝ)(h:0≤x)(k:0≤y):0≤zen x y:=by unfold zen; positivity
-- title independent. 
def lighting (m:ℕ)(α:ℝ)(C:ℝ):=Real.exp (-α/2*m)*C
lemma bulb (m:ℕ)(α:ℝ)(C:ℝ)(h:0≤C):0≤lighting m α C:=by unfold lighting; positivity
section
variable {n m w:ℕ}{f y:Mark (side Y i s)}{S T:Support (More (side Y i s))}
include p D B'
lemma glacier_cost (g0:0≤α)(Qa:Real.exp α+1 ≤ Λ.h)(f0:∀ x, ‖f x‖ ≤ C)(v0:0≤C)(w0:ε+tailCost (V).c (V).C w≤Real.exp (-α))(E₀:0≤ε)(H:Crater w (tailCost (V).c (V).C w) ε (posters Y s i k D p w).bleed.peg S f m false)(F:AtSupport false S f)(υ₀: (Y.voyage i).kick ≤ k)(U₀:Mirror Λ.block (reserve Λ l) (side Y i s) S f T y n): ‖Journey.compass Y i k s y‖ ≤ lighting m α C ^ n * Real.exp (zen ζ (V).C * sites (side Y i s)):=by
 obtain ⟨t,h,E⟩:=Mirror.bullet (Journey.prepared Λ l) U₀ E₀ H F; let a:= lighting m α C; have hu:= bulb m α C v0
 let Z:=(Y.voyage i); let M:= Λ.Ctor (Y.ir i) s; let P:=B'.full i k p; let V':= (V).C; have hc:= (V).posse.value; let w:= posters Y s i k D p w; let b:=180* V'; let f₀:= Steam.frost Λ.K.top.clip WT; let Y₀:=Real.exp (b*sites M); have he:0 ≤ f₀:=frost_nn Λ.K.top.clip WT ((zero_le_one.trans Y.oneP).trans (Vale.crown ..))
 let r:=a^n*Y₀; have hr:0 ≤ r:=mul_nonneg (pow_nonneg hu n) (Real.exp_pos _).le; refine le_trans (Club.toll B' (y ∘ drawn ((Y.voyage i).CapeT s)) hr υ₀ p ?_) (le_of_eq (by unfold r Y₀ zen; rw [mul_assoc,←Real.exp_add]; change a^n * Real.exp (b*sites M + ζ*sites M)= a^n * Real.exp ((ζ+b)*sites M); rw [add_mul ζ b,add_comm (b*_)]));
 intro x; let c:=Steam.τ Λ.W WT M; let δ:= Steam.υ Λ.K.top.clip WT x.1; have hδ:0≤δ:= mul_nonneg (Nat.cast_nonneg _) he
 apply le_trans (cashout Λ.U w E P.book g0 hc.le Qa (enough_y ..) (level_p _).le (cash_v _) w0 x ((posters_p Y s i).paid _)) ?_
 let d₀:= Fintype.card (Single M); have hy:=U₀.cost f0 (x.1,Q x); have hΘ: Real.exp (-α)^t ≤ Real.exp (-α/2*m)^n:=by
    have hφ : (m:ℝ)*(n:ℝ)≤ 2*t:= by exact_mod_cast h
    rw [←Real.exp_nat_mul,←Real.exp_nat_mul]; apply Real.exp_monotone; nlinarith only [mul_le_mul_of_nonneg_left hφ g0]
 have hB:(1+V')^d₀ ≤ Y₀:=by
    have hx: (d₀:ℝ)≤ 180*sites M :=(Pic.units_t ..).trans_le (by
        unfold sites; gcongr -- tune
        · exact (Nat.le_mul_of_pos_right _ two_pos))
    apply le_trans (pow_le_pow_left₀ (show 0≤1+V' by unfold V'; linarith) ((Real.add_one_le_exp V').trans' (add_comm (1:ℝ) _).le) d₀); unfold Y₀; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; exact (mul_le_mul_of_nonneg_right hx hc.le).trans_eq (by unfold b; ring)
 change Real.exp (-α)^t * ‖y _‖ * (Real.exp c * (1+V')^d₀) ≤ r * Real.exp (c+δ)
 apply (mul_le_mul (mul_le_mul hΘ hy (norm_nonneg _) (by positivity)) (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le (pow_nonneg (show 0 ≤ 1+V' by unfold V'; linarith) _)) (mul_nonneg (by positivity) (pow_nonneg v0 _))).trans
 refine (mul_le_mul_of_nonneg_left (Real.exp_monotone (show c ≤ c+δ from le_add_of_nonneg_right hδ)) hr).trans' ?_; unfold r a lighting; rw [mul_pow]; refine le_of_eq (by ring)
end
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
