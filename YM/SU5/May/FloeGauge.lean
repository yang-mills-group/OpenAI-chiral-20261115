import YM.SU5.Reconstruction.Oblique.Consulting
import YM.SU5.Reconstruction.Hygrometry.Sandy
import YM.SU5.May.FloeProof
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
open RG Wilson Phase Mir Vale Vale.Grace Peaks Paige Vault
open Stationary (Gaia)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open scoped ComplexOrder
local notation "I"=>Complex.I
variable {K: Pressure.Teller group} {P: Patch}{B:Side}{e:ℝ}{Y:Pricing K.j P.L P.odd_side (Thread K.j)}(A:Grasp Y B e)(g:0≤e)(h:1≤K.j) (p:Pearl A) (u:Stamped K.j P.L P.odd_side Y)
variable {m: Side}(R:Ramp)(M:Jill.Male)(k:A.roundZ ≤ (CSide m B).val)
local notation "Ta"=> CSide m B
local notation "J"=> R.vehicle Ta
local notation "Ω"=> mateK Ta
local notation "ξ"=> changeM (m:=m) A 1 M
include g h p u k
-- cross reality Spin at actual orbit unity; all Male.
lemma spin_mirror (F:FC (Single (CSide m B))): SpinPrice (changeM A (1:Skye.Pane (CSide m B)) M) (theta (R.vehicle (CSide m B)) F)=star (SpinPrice (changeM A (1:Skye.Pane (CSide m B)) M) F):=by
 have ht:R.turnLink (CSide m B) 1=1:= by rw [R.turn_pull]; funext e; unfold Lattice.pull Step.read; split <;> simp
 let P':= R.plan; have Q:Spire.arum J false true Ω ξ= ξ:=by
    rw [show J=prepU P' R.reel (xtra false) _ from rfl,change_g p u k h _ (atlas_guard g) M P' false R.reel R.jet]; exact congrArg (fun x=>changeM A x M) ht
 let Q:=Q -- shadow
 let W(F:FC (Single (CSide m B))):ℂ:=inner ℂ Ω (acts F ξ)
 have he(F:FC (Single Ta)): W (theta J F)=star (W F):=by
    unfold W; nth_rw 1 [←Q]; rw [show theta J F= tourP J false true F from rfl,← arum_act]; nth_rw 1 [← arum_self (q:=Ω) J false true (Tset Ta) ((touchP Ta) ▸ tickB Ta) (tickR P' inert R.reel R.jet Ta)]; exact arum_globe J false true (Tset Ta) ((touchP Ta) ▸ tickB Ta) (tickR P' inert R.reel R.jet Ta) _ _
 have hv := he 1; rw [theta_one] at hv; unfold SpinPrice; rw [star_div₀,show inner ℂ Ω (acts _ ξ)=star (W F) from he F]; change _ = star (W F)/star _; rw [← show W 1=inner ℂ Ω ξ from (by unfold W; rw [act_one])]; exact congrArg (star (W F) / ·) hv -- tune
variable (w: Pad K.j (CSide m B))
variable {α:Type*}(s t:Personality)(x y:Cover)
local notation "K↑"=> whisper R
local notation "k↑" s:max=> (whisper R).role s
local notation "D" x:max=> (whisper R).cell x
include w
omit k p u g in
private lemma q_pair (W:Wave (Single Ta))(f:Sea (latPose K.j M Ta) W): ice K.j Ta M 1 x y s t= SpinPrice W (ton (player Ta x 1 s)*ton (player Ta y 1 t)):=by
 let Q(b:Bool):=if b then s else t; let L(b:Bool):=if b then x else y
 let X(k:Bool):=player Ta (L k) 1 (Q k); have hp:= reckons M w.1 h f X (fun i=>player_tones ..) [true,false]; rw [Hygrometry.duo] at hp; change _=SpinPrice W (ton (X true)*ton (X false)); apply Eq.trans hp.symm; apply congrArg; change _=ton (X true)*ton (X false); unfold rollC; simp [comp_def]
include w
lemma coin_mirror : ActMark.applause s.down * ActMark.applause t.down * ice K.j Ta M 1 (D x) (D y) (k↑ s) (k↑ t)=star (ice K.j Ta M 1 x y s t):= by
 let ζ:=ξ; have he: Sea (latPose K.j M Ta) ζ:=overhead A g k w M; rw [q_pair h M w _ _ (D x) _ ζ he, q_pair h M w s t x y ζ he, ←spin_mirror A g h p u R M k]; rw [theta_mul]; change _=SpinPrice _ (theta ((K↑).turnout Ta) (ton (player Ta x 1 s))*theta ((K↑).turnout Ta) (ton (player Ta y 1 t))) -- `(K↑).turnout` needs N
 rw [(K↑).lets,(K↑).lets, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,SpinPrice.cash,SpinPrice.cash]; ring
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.coin_mirror
