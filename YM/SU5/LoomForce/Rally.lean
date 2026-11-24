import YM.SU5.LoomForce.Basin
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
open Next.Rank Spindle
open Buffered Pannier Pannier.Chancel Rous Afterglow
open Py Py.Rate Py.Rate.LocalLimit Preparation Preparation.Yoke
open Afterglow.Tower.VacuumSelection.Spine
open Gleam Gleam.Wake Regis.Head Regis.Wake Tempest Pressure BProof Worth Worth.Pays WakeInvestment
-- `Loose Q` keeps first x-exponent (important in extrapolated refinement with cap powers)
def Loose (Q:ℝ)(f:ℝ→ℝ):Prop := ∃ q, Worth.Pays Q q 0 f
namespace Loose
variable {g t e q:ℝ}{f h:ℝ→ℝ}
lemma fixed (x:ℝ): Loose 0 (fun _=>x):=⟨0,constant x⟩
lemma meter (q b:ℝ):Loose q (fun x=>coin x q b 0):= ⟨b,whole ..⟩
lemma scaled (p:Loose q f)(l:ℝ):Loose q (fun x=> l*f x):= by obtain ⟨t,h⟩:=p; exact ⟨t,Pays.scale l h⟩ -- autoImplicit q oops
lemma right (p:Loose q f)(l:ℝ): Loose q (fun x=> f x*l):=by obtain ⟨t,h⟩:=p; exact ⟨t,Pays.right l h⟩
lemma add (p:Loose g f)(u:Loose g h): Loose g (fun x=> f x+h x):=by
 obtain ⟨a,p⟩:=p; obtain ⟨b,t⟩:=u; refine ⟨max a b +1, plus (merit p (Or.inr (Or.inl ⟨rfl,?_⟩))) (merit t (Or.inr (Or.inl ⟨rfl,?_⟩)))⟩
 · linarith only [le_max_left a b]
 linarith only [le_max_right a b]
lemma mix {Q:ℝ}(p:Loose g f)(u:Loose t h)(e:g+t=Q): Loose Q (fun x=> f x*h x):=by
 obtain ⟨a,p⟩:=p; obtain ⟨b,t'⟩:=u; exact ⟨a+b,by simpa only [e,zero_add] using times p t'⟩
lemma uplift {x:ℝ}(p:Loose g f)(t:g≤x): Loose x f:=by
 obtain k|k:= t.lt_or_eq; · obtain ⟨a,p⟩:=p; exact ⟨a,merit p (Or.inl k)⟩
 exact k ▸ p
lemma rise {x:ℝ}(p:Loose g f)(n:ℕ)(e:g*n=x): Loose x (fun u=> f u^n):=by
 obtain ⟨a,p⟩:=p; exact ⟨a*n,by simpa only [e,zero_mul] using pot p n⟩
lemma toMark (p:Loose 0 f) : ∀ᶠ K:ℝ in atTop, ∀ᶠ x in atTop, f x ≤ coin x 0 K 0 :=by
 obtain ⟨K,p⟩:=p; exact (eventually_gt_atTop K).mono fun u t=>leap p (Or.inr (Or.inl ⟨rfl,t⟩))
lemma throw (p:Loose g f)(t:g<v): ∀ᶠ x in atTop, f x ≤ coin x v e 0:=by obtain ⟨K,p⟩:=p; exact leap p (Or.inl t)
lemma vanishes (p:Loose g f)(t:g<0): Tendsto f atTop (𝓝 0):=by obtain ⟨K,p⟩:=p; exact Pays.limit p (Or.inl t)
lemma paneMeter : Loose 0 (fun x=> (radiusB x:ℝ)):= ⟨1,merit rising (by norm_num [Earlier])⟩
lemma plasma : Loose (-1/2) temp := ⟨1,Pays.fix (whole (-1/2) 1 0) ((eventually_gt_atTop (0:ℝ)).mono fun _ p=> thresh_eq p)⟩
lemma sqRoot : Loose (1/2) (fun x:ℝ=>2*Real.sqrt x) := ⟨0,Pays.fix (Pays.scale 2 (whole (1/2) 0 0)) ((eventually_gt_atTop (0:ℝ)).mono fun x p=>by rw [Regis.Head.Garland.era x p])⟩
lemma skylineL : Loose (-3/10) skyline:= (by convert meter (-120000/400000) 0 using 1; norm_num)
end Loose
open LocalLimit
#check @ManageBud

variable (Λ:Preparation) (C u:ℝ) (V:Rules group) (D J D₀:ℝ)
-- D arbitrary support via eventually rental D≤q(K). J parameter of m^4, actual J for Zoom. D₀ >0 not really needed at this stage.
local notation "X_" s:max => (Vale.hat Λ.R.L Λ.x s)
local notation "B_" s:max => radiusB (X_ s)
local notation "c_" t:max s:max => sPow Λ s t
local notation "w_" s:max => c_ J s^ (4:ℕ)
local notation "f_" x:max => coin x 0 J 0
local notation "Xρ" x:max => 2*Real.sqrt x

structure Articles (Λ:Preparation)(K C D J D₀ u:ℝ)(V:Rules group)(s:ℕ): Prop where
 cap(e:ℕ)(p:(e:ℝ)≤ sPow Λ s D): (2*(e:ℝ)+1)^4 ≤ sPow Λ s K
 panels : (Fintype.card (Panels (radiusB (Vale.hat Λ.R.L Λ.x s))):ℝ) ≤ sPow Λ s K
 level : creditJ ≤ radiusB (Vale.hat Λ.R.L Λ.x s)
 neck : Mantle V (radiusB (Vale.hat Λ.R.L Λ.x s)) (temp (Vale.hat Λ.R.L Λ.x s)) u
 fuel (ρ:ℝ)(p: |ρ| ≤ 2*bornQ Λ s):
    let x := Vale.hat Λ.R.L Λ.x s; let A:= sPow Λ s J ^ 4; let B:= radiusB x
    ManageBud (A*ρ^2*age C B (temp x)) (A*ρ^2*allErrorMax V C B (temp x) (skyline x)) (A*(2*D₀)) (scratch x) (sPow Λ s K)
lemma panelSize (B:ℕ): Fintype.card (Panels B) ≤ 2*(((2*B+1)^4*Fintype.card PlaqAxes)*Fintype.card group.ColorIndex):=by
 have hp : Fintype.card (Turn B) ≤ (2*B+1)^4*Fintype.card PlaqAxes:=by
    rw [show Fintype.card (Turn B)= (Device B).card from Fintype.card_coe _ ,Device]; apply (card_filter_le ..).trans; simp [Corona.box_size,two_mul] -- adjust
 unfold Panels Sheds; rw [Fintype.card_prod,Fintype.card_bool,Fintype.card_prod]; exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hp)

lemma rallies (c:0≤ C)(h:0<u): ∀ᶠ K:ℝ in atTop, ∀ᶠ s in atTop, Articles Λ K C D J D₀ u V s:=by
 let f(x:ℝ) := coin x 0 J 0^4; let a(x:ℝ) := f x*((2*Real.sqrt x)^2); let L(x:ℝ):= (4*(radiusB x:ℝ)); let P(x:ℝ):= L x*temp x
 let t(x:ℝ):= 2*P x
 let W(x:ℝ) := a x *age C (radiusB x) (temp x)
 let Q(x:ℝ) := a x *allErrorMax V C (radiusB x) (temp x) (skyline x)
 let q(x:ℝ):= (radiusB x:ℝ); let S(x:ℝ):=2*q x+1
 have v : Loose 0 L := Loose.paneMeter.scaled _
 have hf : Loose 0 f:= (Loose.meter 0 J).rise 4 (by norm_num)
 have ha:Loose 1 a := hf.mix (Loose.sqRoot.rise (x:=1) 2 (by norm_num)) (by norm_num)
 have hp : Loose (-1/2) P:= v.mix Loose.plasma (by norm_num); have ht : Loose (-1/2) t:= hp.scaled 2
 have hw : Loose 0 W:= ha.mix (((ht.rise (x:= -3/2) 3 (by norm_num)).scaled C |>.uplift (by norm_num)).add ((ht.rise (x:= -1) 2 (by norm_num)).scaled _)) (by norm_num)
 have he₀ : Loose (-4/5) (fun x=> rawError V (P x) (radiusB x) (temp x) (skyline x)):=by
    apply Loose.add
    · exact (((hp.rise (x:= -1) 2 (by norm_num)).scaled _).uplift (by norm_num))
    apply v.mix _ (show (0:ℝ)+(-4/5)=-4/5 by norm_num)
    exact (((v.mix Loose.skylineL (Q:= -3/10) (by norm_num)).scaled (2*group.colorScale)).mix Loose.plasma (by norm_num)) -- fix
 have he : Loose (-3/10) Q := by
    apply ha.mix _ (show (1:ℝ)+(-13/10)=-3/10 by norm_num); apply Loose.add
    · apply Loose.add ((ht.rise (x:= -3/2) 3 (by norm_num)).scaled C |>.uplift (by norm_num))
      exact (he₀.scaled ((2:ℝ)⁻¹*C)).mix (ht.add hp) (by norm_num)
    exact (((((Loose.skylineL.scaled (2*group.colorScale)).mix Loose.plasma (Q:= -4/5) (by norm_num)).mix v (Q:= -4/5) (by norm_num)).scaled C).mix hp (by norm_num))
 let α(x:ℝ):=f x*(2*D₀); have hy:Loose 0 α:=hf.right _; let ξyy:=hy.mix hy (Q:=0) (by norm_num)
 let j(x:ℝ):= (2*coin x 0 D 0+1)^4; have jx: Loose 0 j:= ((((Loose.meter 0 D).scaled 2).add (Loose.fixed 1)).rise 4 (by norm_num))
 let N':= Fintype.card group.ColorIndex; let n:= Fintype.card PlaqAxes; let k(x:ℝ):= 2*(S x^4 * (n:ℝ)*N'); have hk:Loose 0 k:= (((((Loose.paneMeter.scaled 2).add (Loose.fixed 1)).rise 4 (by norm_num)).right n |>.right N').scaled 2)
 filter_upwards [hw.toMark, jx.toMark, hk.toMark, (hw.rise (x:=0) 2 (by norm_num)).toMark,hy.toMark,(ξyy.add ξyy).toMark] with K w r ℓ wa y z
 let Kζ:= (hw.scaled 2).mix he (Q:= -3/10) (by norm_num) |>.add ((he.rise (x:= -3/5) 2 (by norm_num)).uplift (by norm_num))
 have w0:= V.positive; have hC:= SU.group.colorScale_pos; let T:=turnover Λ
 filter_upwards [T.eventually w,T.eventually (hp.vanishes (by norm_num) |>.eventually (ge_mem_nhds V.radius)), T.eventually (ht.vanishes (by norm_num)|>.eventually (ge_mem_nhds h)), T.eventually r,T.eventually ℓ,T.eventually wa,T.eventually y,T.eventually z,T.eventually (he.throw (e:=0) (v:= -7/400000) (by norm_num)),T.eventually (Kζ.throw (e:=0) (v:= -7/400000) (by norm_num)), T.eventually (Work.E08.eventual_radiusB creditJ)] with s w L₀ t r ℓ w₁ h h' hv ht b
 let B:= B_ s; let x:=X_ s
 refine ⟨fun e p=>le_trans ?_ r,le_trans ?_ ℓ,b,⟨L₀,t⟩,?_⟩
 · unfold j; change (2*(_ :ℝ)+1)^4≤(2*(sPow Λ s D)+1)^4; gcongr
 · change ((Fintype.card (Panels B)):ℝ) ≤ k x; unfold k S q; exact_mod_cast panelSize (B_ s)
 intro ρ p X A R; let w:=temp X; have wp:0≤w:=Work.E04.temp_nonneg _; have hf:0≤ A:= by apply pow_nonneg (BProof.coin_pos ..|>.le)
 have hx: 0≤age C R w:= by unfold age broadCash; positivity
 have he:0≤ allErrorMax V C R w (skyline X):=by have hS:0≤ skyline X:=(WakeInvestment.chip_pos ..).le; unfold allErrorMax broadError extraDrift rawError; simp only; positivity
 let C':=A*ρ^2*age C R w; let W':=A*ρ^2*allErrorMax V C R w (skyline X); have hc:0≤A*ρ^2:=mul_nonneg hf (sq_nonneg _); have hq:0≤C':=mul_nonneg hc hx; have hw:0≤W':=mul_nonneg hc he; have h₀:A*ρ^2≤a x:= by apply mul_le_mul_of_nonneg_left _ hf; rw [←sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) p _
 have h₁:C'≤ W x:=mul_le_mul_of_nonneg_right h₀ hx; have h₂:W'≤ Q x:=mul_le_mul_of_nonneg_right h₀ he
 refine ⟨h₁.trans (by assumption), (pow_le_pow_left₀ hq h₁ 2).trans w₁,h₂.trans hv, le_trans ?_ ht,h,h'⟩
 change 2*C'*W'+W'^2≤2*W x* Q x+Q x^2; gcongr
#print axioms rallies
end YM.CF.LitCurrent.Surplus
