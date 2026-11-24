import YM.SU5.May.TorqueRange
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.TorqueBeam
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
local notation "Ω" => Complex.I
open May.Floe
open Buffered Buffered.Advance Buffered.Advance.Whorl May.Arctic
variable {K: Pressure.Teller group} {P: Patch}{B:Side}{e:ℝ}{Y: Pricing K.j P.L P.odd_side (Thread K.j)}(A:Grasp Y B e)(g:0≤e)(h:1≤K.j) (p:Pearl A) (u:Stamped K.j P.L P.odd_side Y)
variable {m:Side}(R:Ramp)(M:Jill.Male)(k:A.roundZ ≤ (CSide m B).val)(w:Pad K.j (CSide m B))
variable {α:Type*} (X:α→ Reader0 (Single (CSide m B)))
local notation "N"=> CSide m B
local notation "Σ"=> changeM (m:=m) A 1 M
local notation "U"=> R.vehicle (CSide m B)
local notation "S"=> Tset (CSide m B)
local notation "K₀"=> ledger (CSide m B) K.j M
variable {W:Finset (Single (CSide m B))} (ρ δ:ℝ) (hw:∀ i,Worth (Tset (CSide m B)) W ρ (X i))(pc:0≤ρ) (dC:0≤δ)
variable {β:Type*}[Fintype β](F:β→List α)(w':β→ℂ)(b:Bool)(t:∀ i,wheat (F i)=b)
local notation "Λ" => costal ∘ X
private lemma chord_size (l:List α)(e: wheat l=b): Reflect.chord b= (if l.length%2=0 then 1 else Ω):=by
 rw [Hygrometry.wheat_grade] at e; rw [←e]; by_cases h:l.length%2=0 <;> unfold Reflect.chord <;> split_ifs <;> grind
private lemma v_part(C:List α):theta U (rollC (ton ∘ X) C)=veil (costal∘X) C • (rollC (ton∘ (send U ∘ X)) C):=by
 induction C with
 | nil=> simp [rollC,veil,theta_one,one_smul]
 | cons i C ih=> unfold rollC veil at *; simp only [List.map_cons,List.prod_cons,theta_mul]; rw [ih]; unfold Function.comp; rw [mark_send,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
local notation "Oₗ" => rollC (ton ∘ X)
local notation "Lz" j:max=> rollC (ton ∘ bag U X) j
include g k w h hw t
set_option maxHeartbeats 600000 in
lemma yielded : SpinPrice Σ (poseX (whisper R) b (∑ i,w' i • Oₗ (F i)))= ∑ i,∑ j,star (w' i)*thaw (costal ∘ X) (focusL U K₀ X) (F i) (F j)*w' j:=by
 let z:= bag U X; let Z:= ton ∘ z
 have hv(i:α⊕α): KeyT (z i) (tickA N):=by cases i with| inl i=>exact markSend R (chargeable ((hw i).limb))| inr i=>exact chargeable ((hw i).limb)
 unfold poseX; rw [show (whisper R).turnout N=U from rfl,theta_sum,Finset.sum_mul]; simp_rw [Finset.mul_sum,Finset.smul_sum, SpinPrice.pool]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ 
 rw [theta_smul,v_part R X,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,show rollC _ _*Oₗ (F j)=Lz (pairOrder (F i) (F j)) from ?_]; simp_rw [SpinPrice.cash]; rw [reckons M w.1 h (overhead A g k w M) z hv,thaw,chord_size b _ (t i)]; change (ite _ _ _) * (_ * (_* (_ * runes (focusL U K₀ X) _)))= star _ * _ * _; ring
 unfold pairOrder rollC; simp only [List.map_append, List.prod_append,List.map_map]; rfl
omit g k w h hw t
-- pay quota.Fair
variable [LinearOrder α] [Fintype α]
variable (y z:α⊕α→α⊕α→ℂ)
local notation "d"=> costal ∘ X
local notation "Now" p:max =>∑ i,∑ j, star (w' i)*thaw (costal ∘ X) p (F i) (F j)*w' j
private lemma veil_weight(l:List α): ‖veil (costal∘X) l‖=1:=by induction l with| nil=>simp [veil]| cons i l ih=> rw [show veil (costal∘X) (i::l)=costal (X i)*veil (costal∘X) l from rfl,norm_mul,ih, costal_f,mul_one]
variable (B₁:ℝ) (hc:‖ledger (CSide m B) K.j M‖≤ B₁)
lemma capitalL (ε Z':ℝ) (p:1≤Z') (e: 0≤ ε)(Y:∀ i j,‖y i j‖ ≤ Z')(W:∀ i j,‖z i j‖ ≤ Z')(L:∀ i j,‖y i j-z i j‖ ≤ ε) (κ:ℕ)(h:∀ i, (F i).length ≤ κ): ‖(Now y)-(Now z)‖ ≤ rimeCost κ Z' * ε * (∑ i:β,‖w' i‖)^2:=by
 let B0:=rimeCost κ Z' * ε; have h(i j:β) : ‖thaw d y (F i) (F j)-thaw d z (F i) (F j)‖≤ B0:=by
    unfold thaw; rw [← mul_sub,norm_mul,norm_mul (ite ..),veil_weight]; set t:= (if (F i).length%2=0 then (1:ℂ) else Ω); rw [show ‖t‖=1 from by unfold t; split <;> simp,mul_one,one_mul]
    have he: (pairOrder (F i) (F j)).length≤ 2*κ:=by simp only [pairOrder,List.length_append,List.length_map]; have i:=h i; have j:=h j; omega
    exact (ballots p e y z Y W L _ _ he).trans_eq (by unfold B0 rimeCost; ring)
 rw [←sum_sub_distrib]; refine (norm_sum_le ..).trans ?_; simp_rw [←sum_sub_distrib]; rw [sq]; set X':=(∑ i:β,‖w' i‖); change _≤ B0*(X'*_); rw [←mul_assoc]; nth_rw 2 [mul_comm _ X']; -- fragile
 unfold X'; simp_rw [Finset.sum_mul,Finset.mul_sum]; refine sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=>?_); rw [←_root_.sub_mul,←mul_sub (star _),norm_mul,norm_mul,norm_star]; gcongr; exact h i j
include g k w h hw t pc dC hc p u
lemma purchased (a:WickPlate U K₀ δ S W)(κ:ℕ)(he:∀ i,(F i).length≤κ): -(rimeCost κ (1+(B₁+δ)*ρ^2)*(δ*ρ^2)*(∑ i:β,‖w' i‖)^2) ≤ (SpinPrice Σ (poseX (whisper R) b (∑ i,w' i • Oₗ (F i)))).re:=by
 let Y₀:=focusL U K₀ X; let Z₀:=focusBig U K₀ δ X
 let Y:=Now Y₀; let Z:=Now Z₀
 have hf:0 ≤ Z:=by
    apply wick_honoured (costal∘X) Z₀  -- maybe order? no need
    · exact fun i=> costal_ne (X i)
    · intro i j; exact rear A g h p u R M k w (chargeable (b:= X i) (hw i).limb) (chargeable (b:= X j) (hw j).limb)
    · exact fun i j=> rank_flip K₀ (X i) (X j)
    unfold Z₀; rw [treasury]; exact raiseP U K₀ δ X hw a
 have hm:= Complex.le_def.mp hf; let Z1:=1+(B₁+δ)*ρ^2
 have hW:0≤ B₁:=(norm_nonneg _).trans hc; have hd:0≤ δ*ρ^2:=(by positivity); have hy(i j):‖Y₀ i j‖≤ B₁ * ρ^2:=(focusCharge U K₀ ρ X pc (fun i=>(hw i).budget) i j).trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _)); have hf(i j):‖Z₀ i j-Y₀ i j‖ ≤ δ*ρ^2:=subsidy U K₀ δ ρ X dC pc (fun i=>(hw i).budget) i j
 have hx: ‖Z-Y‖≤ rimeCost κ Z1* (δ*ρ^2)*(∑ i:β,‖w' i‖)^2:=capitalL X F w' Z₀ Y₀ (δ*ρ^2) Z1 (le_add_of_nonneg_right (by positivity)) hd (fun i j=>by unfold Z1; linarith only [add_mul B₁ δ (ρ^2), hy i j,hf i j,norm_le_norm_sub_add (Z₀ i j) (Y₀ i j)]) (fun i j=>by unfold Z1; linarith only [add_mul B₁ δ (ρ^2), hd,hy i j]) hf κ he
 rw [yielded A g h R M k w X ρ hw F w' b t]; change _ ≤ Y.re; have ht: Z.re-Y.re ≤ rimeCost κ Z1*(δ*ρ^2)*(∑ i:β,‖w' i‖)^2:= (Complex.re_le_norm (Z-Y)).trans hx; unfold Z1 at ht; linarith [show 0 ≤ Z.re from hm.1]
#print axioms yielded
#print axioms purchased
end YM.CF.May.TorqueBeam
