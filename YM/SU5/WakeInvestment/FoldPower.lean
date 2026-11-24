import YM.SU5.WakeInvestment.TenderScale
set_option synthInstance.maxSize 24000
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph

variable {z A c:ℝ}
set_option quotPrecheck false
local notation "L"=> P.R.L
local notation "D"=> P.K.j
local notation "shx" s:max => hat L P.x s
local notation "vℓ" s:max => shieldC (hat L P.x s)
local notation "Ω" s:max i:max => (side Y i s)
local notation "Gξ" s:max i:max k:max => RootBook Y i k s
local notation "ℂk" s:max i:max => (Y.voyage i).CapeT s

open WakeInvestment
local notation "ℰ" s:max => Worth.meterC (shx s)


variable (s i k : ℕ)
local notation "flatP" => spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
local notation "N" s:max i:max => side Y i s
local notation "ηP" s:max => Worth.gateC (shx s)
local notation "ptQ" s:max i:max k:max => ((RootBook Y i k s).p)
open Rous


attribute [local instance] opCStarAlgebra

open Lamour.Bridge Celeste Clock Hookah
open Cliplet
open Window Buffered.Afterglow.Tower Ballad SitSpin
open Signal.Interval (separationCost)
variable {H:Real.exp 1≤ P.x} {χ d d':ℝ}
variable {I:Type*} [Fintype I] (u:I→Lead.Clan) (G:List I)(x:I→ Cover)(w:I→Twah.DirSpin)(R:ℕ)

variable {E A v:ℝ} {φ μ π κ:ℕ→ℕ} {E' : ℕ→ Buffered.Family (tent Y H) →ℂ}{X:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}
variable {D₀:ℕ→Buffered.Family (tent Y H)→Buffered.Family (tent Y H)}
-- R_s p^{U}. Use /2 ceiling always *positive* beyond this threshold. Keeps cut prices unchanged.
abbrev zoomR (P:Preparation)(A:ℝ)(s:ℕ) := ⌈sPow P s A /2⌉₊
abbrev frayR (P:Preparation)(A:ℝ)(s:ℕ): ℝ:=sPow P s A / (2*(zoomR P A s:ℝ))

lemma sPower_eq (P:Preparation)(s:ℕ)(U:ℝ) : sPow P s U=(sPow P s 1)^U:=by rw [sPow,sPow,BProof.coin_rpow,one_mul,zero_mul]
lemma sPower_pay (P:Preparation)(p:0<A) : Tendsto (fun s:ℕ=> sPow P s A) atTop atTop:=tendsto_atTop.2 fun x=> grow_e A x p P
lemma zoom_grows (P:Preparation)(p:0<A) : Tendsto (zoomR P A) atTop atTop:= tendsto_nat_ceil_atTop.comp (Tendsto.atTop_div_const (by norm_num) (sPower_pay P p))
lemma fray_le (P:Preparation)(s:ℕ)(A:ℝ): frayR P A s ≤1:=by
 let g:=sPow P s A; let z:ℝ:=zoomR P A s; have hp:0<g:=BProof.coin_pos ..; have hz:g/2 ≤ z:= Nat.le_ceil _; change g/(2*z) ≤ _; have ht:0<z:=(half_pos hp).trans_le hz; apply (div_le_iff₀ (show 0<2*z from by positivity)).mpr; linarith only [hz]
lemma fray_p (P:Preparation)(s:ℕ)(A:ℝ): 0<frayR P A s:=by
 let g:=sPow P s A; let z:ℝ:=zoomR P A s; have hp:0<g:=BProof.coin_pos ..; have hz:g/2 ≤ z:= Nat.le_ceil _; change 0< g/(2*z); have ht:0<z:= (half_pos hp).trans_le hz; positivity
lemma fray_lift (P:Preparation)(p:0<A): Tendsto (frayR P A) atTop (𝓝 1):=by
 have hx:Tendsto (fun s:ℕ=> sPow P s A/2) atTop atTop:=(Tendsto.atTop_div_const (by norm_num) (sPower_pay P p))
 have he:= tendsto_nat_ceil_div_atTop.comp hx; have hq:= he.inv₀ one_ne_zero
 rw [inv_one] at hq; apply hq.congr; intro s; let x:=sPow P s A; change ((zoomR P A s:ℝ)/(x/2))⁻¹=x/_; rw [inv_div]; ring_nf

lemma factor_pay (P:Preparation){t:ℝ}(p:0<A) (B:ℕ)(v:t>A*3*B): ∀ᶠ s:ℕ in atTop, (factor (zoomR P A s))^B ≤ sPow P s t:=by
 let N':ℝ:=Fintype.card SU.Slot; let f(x:ℝ):=BProof.coin x 0 A 0; let G(x:ℝ):=f x ^ 3*N'; let W:Worth.Pays 0 (A*3) 0 G:= by simpa only [zero_mul,Nat.cast_ofNat] using Pays.right N' (Pays.pot (Pays.whole 0 A 0) 3)
 have h: Worth.Pays 0 ((A*3)*B) 0 (fun x=>G x^B):=by simpa only [zero_mul] using Pays.pot W B
 filter_upwards [grow_e A 2 p P, (turnover P).eventually (Pays.leap h (p:=t) (w:=0) (q:=0) (Or.inr (Or.inl ⟨rfl,v⟩)))] with s q α
 apply le_trans _ α; let x:=hat P.R.L P.x s; have hq:(zoomR P A s:ℝ)≤ f x:=by have hx: (zoomR P A s:ℝ)< ((f x)/2+1):=Nat.ceil_lt_add_one (half_pos (BProof.coin_pos ..)).le; change 2 ≤ f x at q; linarith only [hx,q]
 unfold SitSpin.factor; change (_* _)^_ ≤ (G x)^_; unfold G N'; gcongr
open Lifted Onyx
abbrev gaugeRise (P:Preparation)(s:ℕ)(U:ℝ)(x:Cover):Stationary.Gaia:= riseX (sPow P s U) (nodeC x)
-- Unit phases budget wraps paid separately. require Spill at actual layouts r lattice heights
omit [Fintype I] in
lemma breadth_pay (P:Preparation) (p:0<A)(Q:ℕ)(u:A<v) : ∀ᶠ s:ℕ in atTop,∀ (x:I→ Cover)(_:Twah.Spill (SitSpin.rest x w) (Q:ℝ) d (zoomR P A s)), 2*(Celeste.breadth (nodeC 0) (lay x G):ℝ) ≤ sPow P s v:=by
 let V:= fun z:ℝ=> BProof.coin z 0 A 0; let B':ℝ:= 4*(Q:ℝ)
 filter_upwards [zoom_grows P p|>.eventually_gt_atTop 0, grow_e A 2 p P,(turnover P).eventually (Pays.leap (Pays.scale B' (Pays.whole 0 A 0)) (Or.inr (Or.inl ⟨rfl,u⟩) : Worth.Earlier 0 A 0 0 v 0))] with s g α t1 x β
 let X:=hat P.R.L P.x s; let K:=zoomR P A s; have hK:0< (K:ℝ):=Nat.cast_pos.mpr g; have hn:(K:ℝ)≤V X:=by have h:(K:ℝ)< V X/2+1:= Nat.ceil_lt_add_one (half_pos (BProof.coin_pos ..)).le; change 2 ≤ V X at α; linarith only [α,h]; -- indent
 let F:I→Twah:= SitSpin.rest x w; let z:= 2*Q*K; let S:=lay x G; have hx : Celeste.breadth (nodeC 0) S ≤ z:=by
    apply Finset.sup_le; intro i l; obtain ⟨i,p,rfl⟩:= List.mem_map.mp (List.mem_toFinset.mp l); apply Finset.sup_le; intro j _; have w:‖riseX K (x i)‖ ≤ (Q:ℝ):= by
       have hf:= β.1 (i,false); rw [dist_zero_right] at hf; exact hf
    have hp: |(x i j:ℝ)| ≤ (Q*K:ℝ):= by
       have ht:(|(x i j:ℝ)/(K:ℝ)|) ≤ (Q:ℝ):= (PiLp.norm_apply_le (riseX K (x i)) j).trans w; rw [abs_div, abs_of_pos hK] at ht; exact (div_le_iff₀ hK).mp ht
    change ((nodeC 0 j - (nodeC (x i)) j)).natAbs ≤ z; have hf: (x i j).natAbs ≤ Q*K:=by apply (Nat.cast_le (α:=ℤ)).mp; rw [Int.natCast_natAbs]; exact_mod_cast hp -- norm_cast
    have hy:nodeC 0 j - nodeC (x i) j= -(2*x i j):=by unfold nodeC; simp [two_smul,two_mul]
    unfold z; rw [hy,Int.natAbs_neg,Int.natAbs_mul]; change 2*_ ≤ _; rw [mul_assoc]; omega
 apply le_trans _ t1; change 2* (Celeste.breadth (nodeC 0) S:ℝ) ≤ B'*V X; have he := Nat.cast_le (α:=ℝ) |>.mpr hx; unfold z at he; push_cast at he; unfold B'; nlinarith only [he,mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α:=ℝ) Q)]

variable (V:Universal Y H φ μ X E') (Q:Coherent (i:=φ) (k:=μ) (E:=E') Y H D₀ π κ)
include V Q
lemma fixedScale (q:Investment P E v)(L_:Dispatchers P)(K:Meritorious P) (p:0<A)(f:0<χ)(b:0<d)(B:ℕ): ∀ᶠ s:ℕ in atTop,∀ (x:I→ Cover), Twah.Spill (SitSpin.rest x w) (B:ℝ) d (zoomR P A s) → ‖E' s (Papal.household (tent Y H) (SitSpin.reader u x w (zoomR P A s) G))-wakeOf u x w (zoomR P A s) G‖≤ χ:=by
 let y:= (G.length:ℝ)+1; have he:0≤(G.length:ℝ):=Nat.cast_nonneg _; let b':=A*4*y; have hb:A < b':=by unfold b' y; nlinarith only [p,he]
 have hf:A*3*G.length< b':=by unfold b' y; nlinarith only [p,he];
 obtain ⟨n,t⟩:= spin_wake (d':=(B:ℝ)) Y u G w V Q q L_ K (p.trans hb) f b
 filter_upwards [t,(factor_pay P p G.length hf),(zoom_grows P p).eventually_ge_atTop n, breadth_pay (G:=G) (w:=w) (d:=d) P p B hb, grow_e b' (G.length:ℝ) (p.trans hb) P] with s hs ht hw hu hz x P'; exact hs _ hw x hz ⟨_, hu _ P'⟩ ht P'
#print axioms fixedScale
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
