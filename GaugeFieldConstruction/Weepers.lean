import GaugeFieldConstruction.Tiaras
set_option autoImplicit false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
open Sour.SliceRoof Fock.Flux
local notation "Xq" s:max => Vale.hat P.R.L P.x s
abbrev attire (j i k:ℕ) (V:Orbit (count Y j i)) (X:Cipher (count Y j i)):=
 let Z:=gram Y j i k; let B:= room Y j i; let N:=count Y j i; let S:=spar P.K.j Z.J.M (B V)
 Graph.past Z V.1 • acts (Complex.exp (-pigment Z.J.I (B V)) • (tank S X * exp (dg (Graph.actF P.K.j Z B V)))) (changeM P.U (B V) Z.J.M)
lemma uses_reg (j i k:ℕ)(V:Orbit (count Y j i)) : Graph.recX P.U (gram Y j i k) (room Y j i) V= attire Y j i k V ((gram Y j i k).board V):= Graph.porch _ _ V
open CF.Pannier.Damask.VelvetP
abbrev nativeCost (j i k:ℕ)(X:Orbit (count Y j i)):ℝ:= lad_z X.1 P.K.top.clip (Xq j) (gram Y j i k).beta
private lemma p3_now {C D a z α b w:ℝ}(j i k:ℕ)(u:j≤Y.uv k)(hp:0<a)(hb:0<b)(s:Signed) (t:Oak Y j i)
 (V:Orbit (count Y j i))(x:Cipher (count Y j i))(h: tier P.h x.val ≤ Real.exp z)(g:|w|≤1) (e:Kea.Pad P.K.j (count Y j i))
 (level:∀ U:Seat (count Y j i) → SU.E, let S:= tradew (count Y j i) U
                  let T:= gram Y j i k; let M:=T.J.M; let N:= count Y j i; let Z:=boardC N P.K.j M
                  PurchB C D w (oneWarp Z (pinShift N P.K.j M) S w) ∧ PurchB C D w (star (onePeak Z (pinBack N P.K.j M) S w)))
 (ht:0≤D)(ht':(1+(b+1/2))*D ≤ P.h) {F:Sour.Elm (count Y j i) Unit P.d a b}(hh:Sour.NearL F (fun _=>hemi_L (count Y j i) P.K.j (gram Y j i k).J.M)) {A B:ℝ} {W:Sour.Elm (count Y j i) Unit P.d A B} (uA:0<A)(uB:0 ≤ B)(uh:Sour.NearL W (fun _ =>Moire.bloom (gram Y j i k).J.P)) (hc:0 < Xq j)(ha:0≤ badgeDust (Xq j))(hB:badgeDust (Xq j) ≤ P.J.k)(hv':0 ≤ suitCost P.R.L (Xq j))(u':P.J.n≤clocks.height (Xq j)) (kV :‖Pec.pigment (gram Y j i k).J.I (room Y j i V)‖ ≤ α):
 let G:= gram Y j i k; let U:= Loose s t.T V.1; let M:=clocks.height (Xq j); let L:= suitCost P.R.L (Xq j); let J:= b+1/2; let Z:= rentK V s t.r (badgeDust (Xq j)) L a b P.d M; let Y':= rentK V s t.r (badgeDust (Xq j)) L A B P.d M
 ‖acts (offWall Y j i k U w) (attire Y j i k V x)‖ ≤ Graph.past G V.1 * Real.exp (z + α + D^2*((1+J)*(J*Y')) + ((Real.exp 1* D)^2+3)*Z):=by
 intro G U M L J Z Y'
 let P':= P.K.j; have hu:1≤P':= by unfold P'; rw [P.kJ]; decide -- tune
 let N:=count Y j i; let Q:=boardC N P' G.J.M; let B':=room Y j i; let F':= spar P' G.J.M (B' V); let X:=pinShift N P' G.J.M; let H:=pinBack N P' G.J.M; let T:=translateW Q X H (tradew N U) w; let A₀:= Graph.actF P' G B' V
 let A':= Z; obtain ⟨eQ,R,eF,gB⟩:= tilt_P P.K.j G hh hp hb.le P.dpos (roofage Y i j) ha hB t.withH t.T V s u' hv' (suit_sizing P.R.L hc t.mark) uh uA uB
 have vP:=token_V e hu G.J.M; have hQ:= baseP e G.J.M
 have zG : ‖T (tank F' x)‖ ≤ Real.exp z:=by
    apply (charter vP hQ x (zero_le_one.trans P.height) _).trans h
    obtain ⟨f',h'⟩:=level U; have he: payFull F' (b+1/2):=by
       have hGuard : Guard (B' V) P.d:= (roofage Y i j).paid V; let S':=halfBand N; let Y':= hemi_L N P' G.J.M (Tulip.profile (B' V))
       have hv: F'=Y'+S':= (sub_add_cancel F' S').symm; have hh:=payFull_real P.dpos (g:=hp) hh (B' V) hGuard
       have hz:=payFull_cast (payFull_blank (Single N)) (1/2); rw [abs_of_nonneg (by norm_num),mul_one] at hz
       rw [hv]; exact payFull_first hh hz
    exact charter_bracket vP hQ he ht' ht (from_local f') (from_local h') -- tune
 have K:=level 1; rw [trade_p] at K
 have hL:=fun x:Single N=>charter_creation (n:=N) x vP hQ K.1 K.2
 have he : ‖T (exp (dg A₀))‖ ≤ Real.exp (D^2*((1+J)*(J*Y'))):=by
    rw [show T (exp (dg A₀))=_ from expChar vP hQ _ _ _]; apply (Graph.bootC _).trans (Real.exp_monotone ?_); exact (charDG vP hQ ht (fun x=>(hL x).1) (fun x=>(hL x).2)).trans (mul_le_mul_of_nonneg_left gB (sq_nonneg D))
 let Yp:= changeM P.U (B' V) G.J.M; let S:= offWall Y j i k U w; obtain ⟨hw,hP⟩:= safety Y j i k V; let Wp:= acts S Yp
 let ze:= (Real.exp 1* D)^2+3; have hr: ‖Wp‖≤ Real.exp (ze*Z):= (shot_L vP hQ g K.1 ht _ hw hP).trans (Real.exp_monotone (mul_le_mul_of_nonneg_left eF (by positivity:0 ≤ (Real.exp 1* D)^2+3)))
 let c':= Complex.exp (-pigment G.J.I (B' V)); have hv:‖T (c' • (tank F' x*exp (dg A₀)))‖ ≤ Real.exp (z+α+D^2*((1+J)*(J*Y'))):=by
    have hh:‖c'‖≤Real.exp α:=(Complex.norm_exp_le_exp_norm _).trans (Real.exp_monotone (le_trans (norm_neg _).le kV)); rw [show T (c' • (tank F' x *exp (dg A₀)))=_ from scale_crest c' _ _ _ _ _ _,norm_smul,translate_prod vP hQ]
    apply le_trans (mul_le_mul hh ((norm_mul_le ..).trans (mul_le_mul zG he (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le)
    apply le_of_eq; rw [Real.exp_add (z+α),Real.exp_add z]; ring
 unfold attire; let q:= Graph.past G V.1
 change ‖acts S (q • acts (c' • (tank F' x*exp (dg A₀))) Yp)‖ ≤ _; rw [←Complex.coe_smul,map_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _|>.le),show acts S (acts (c' • (tank F' x*exp (dg A₀))) Yp)=acts (T (c' • (tank F' x*exp (dg A₀)))) Wp from act_char vP hQ ..,Real.exp_add (_+D^2*_)]
 exact mul_le_mul_of_nonneg_left ((Graph.spentS _ _ _).trans (mul_le_mul hv hr (norm_nonneg _) (Real.exp_pos _).le)) (Real.exp_pos _).le
lemma exhib_T (p:Cash_T P.V P.d P.h) (ε:ℝ)(uε:0<ε):
 ∃ C D:ℝ,0 < C ∧0<D ∧D≤ P.h ∧∀ᶠ j:ℕ in atTop,∀ i k:ℕ,j≤ Y.uv k→
 let G:= gram Y j i k; let M:=G.J.M; let S:=room Y j i; let N:= count Y j i; let X:=boardC N P.K.j M
 Kea.Pad P.K.j N ∧ (∀ (U:Seat N → SU.E)(b:ℝ), |b|≤1→ PurchB C D b (oneWarp X (pinShift N P.K.j M) (tradew N U) b) ∧ PurchB C D b (star (onePeak X (pinBack N P.K.j M) (tradew N U) b))) ∧ ∀ (s:Signed)(T:Oak Y j i)(V:Orbit N)(b:ℝ),|b|≤1→∀ (x:Cipher N)(τ:ℝ), tier P.h x.val ≤ Real.exp τ → ‖acts (offWall Y j i k (Loose s T.T V.1) b) (attire Y j i k V x)‖ ≤ Graph.past G V.1 * Real.exp (τ+ε*nativeCost Y j i k V):=by
 obtain ⟨a,l,b,w,⟨e,f,c,v,hj,W⟩,N0,H,A,D,hA,hD,V0,V⟩:=p; let q:=P.K.top.clip; let L:=P.R.L
 let J:= b+1/2; have hJ:0<J:=by unfold J; linarith only [w]
 let C:=(1+J)*J*D^2 + ((Real.exp 1* D)^2+3)
 have hC:0<C:=by unfold C; positivity
 let δ:= ε/2/C; have ht:0<δ:=div_pos (half_pos uε) hC
 refine ⟨A,D,hA,hD,(le_mul_of_one_le_left hD.le (show 1 ≤ 1+J from le_add_of_nonneg_right hJ.le)).trans V0,?_⟩
 obtain ⟨K,zP⟩:=Kea.gave _ hj; let F:= stage_slope P.V P.x; let R:= P.J.n; let d:=P.d
 filter_upwards [F.eventually (exper L q l w.le P.d P.dpos δ ht), F.eventually (exper L q f v.le P.d P.dpos δ ht),F.eventually (tax_p (t:=P.d) (cash_v P.W.C) q R (level_p P.W.C) P.J.ht (ε/2) (half_pos uε)),F.eventually_gt_atTop 0,F.eventually badge_ok,F.eventually (badgePower.tends (by norm_num) |>.eventually (ge_mem_nhds P.J.ht)), F.eventually (Work.E08.eventual_radiusB P.J.n),count_ages Y N0,count_ages Y K,F.eventually (wall_matures P.R.L)] with j p1 p2 p3 i1 i2 i3 uY ht' tQ u i k p G M N X
 let S:=room Y j i
 let g:= zP _ (even_with Y ..) (tQ i); refine ⟨g, fun U b hb=> V g U _ b hb,?_⟩
 obtain ⟨_,-,hH,y,qL⟩:=prices_plot Y j i k p; obtain ⟨iY,pY⟩:= mint_w Y j i k p; obtain ⟨Z,K,_⟩:=H _ (ht' i) M; obtain ⟨Z',K',_⟩:= W _ _ iY pY
 intro s T X' m g' Yp τ ν
 let t := T.T; let U:= X' ; let Y':= Yp; let x:= Xq j; let b₁:= nativeCost Y j i k X'
 let θ:= badgeDust x; let v₁:=suitCost L x; let d₁:= clocks.height x
 have he:0<θ:= (Work.E09.temp_pos i1).trans_le i2
 have hv:0≤v₁:= (suitFee_pos _ he).le.trans (suit_sizing P.R.L i1 T.mark)
 have hg: d₁≤(More N).val:=by
    have ht: hallBill d₁ ≤ T.r.count.val/2:= u T.r.count T.mark; have hd: 2*(T.r.count.val+1)<(More N).val:= T.withH; unfold hallBill Sequest at ht; omega
 have hy: ‖Pec.pigment G.J.I (S X')‖ ≤ ε/2*b₁:= p3 _ y.1 (roofage Y i j) hg _ _ qL.field.2
 have hl:= p1 _ y.1 N X' s T.r T.oddP T.mark; have hh:= p2 _ y.1 N X' s T.r T.oddP T.mark
 apply (p3_now Y j i k p l w s T X' Yp ν g' g (fun U=>V g U M m g') hD.le V0 K f v.le K' i1 he.le i3 hv uY hy).trans
 apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) (Real.exp_pos _).le
 let a':=rentK X' s T.r θ v₁ a b d d₁; let b':=rentK X' s T.r θ v₁ e c d d₁; let E:= ((Real.exp 1* D)^2+3)
 change a'≤δ*b₁ at hl; change b'≤δ*b₁ at hh; change τ + ε/2*b₁ + D^2*((1+J)*(J* b')) + E*a'≤ τ+ε * b₁
 have hh':=(mul_le_mul_of_nonneg_left hh (show 0≤ (1+J)*J*D^2 by positivity)); have ht : C*δ*b₁ = ε/2*b₁:= by unfold δ; rw [mul_comm C,div_mul_cancel₀ _ hC.ne']
 change ((1+J)*J*D^2+E)*δ*b₁= _ at ht; linarith only [hh',mul_le_mul_of_nonneg_left hl (show 0 ≤ E by unfold E; positivity),ht]
lemma leafUp (L:Side) : RunRate (-(1/2)) 1 (dleaf L):=by
 refine RunRate.mono (p:=RunRate.temps) ?_
 filter_upwards [(SectorNext.Remainder.Scales.year SU.group L).eventually_ge_atTop 1] with y p
 rw [dleaf,abs_mul]; apply mul_le_of_le_one_left (abs_nonneg _)
 unfold SectorNext.Remainder.Scales.g Next.Scheduling.Clock.gap; rw [abs_of_nonneg (by positivity : 0≤ (Real.sqrt (SectorNext.Remainder.Scales.y SU.group L y))⁻¹)]; exact inv_le_one_of_one_le₀ ((by simpa using Real.sqrt_le_sqrt p))
lemma board_grant : ∀ᶠ j:ℕ in atTop,∀ i k:ℕ,j≤Y.uv k →∀ V:Orbit (count Y j i), tier P.h ((gram Y j i k).board V).val ≤ Real.exp (saveZ (Xq j)*Fintype.card (Site (More (count Y j i)))):=by
 filter_upwards [(stage_slope P.V P.x).eventually (logPrice _ _ ((leafUp P.R.L).cmul 3) (c:= -gratuity/2) (w:=0) (d:=0) (by norm_num [gratuity]) one_pos)] with j V i k p v
 apply (charge_struct _ _ _ _ _ _ (prices_plot Y j i k p).2.2.2.2 (zero_le_one.trans P.height) _).trans (Real.exp_monotone _)
 rw [site_card,Nat.cast_pow]; apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg _) _); change 3*_≤1* saveZ _ at V; linarith only [V]
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
