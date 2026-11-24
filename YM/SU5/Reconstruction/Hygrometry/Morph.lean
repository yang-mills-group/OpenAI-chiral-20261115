import YM.SU5.Reconstruction.Hygrometry.Probe
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
open Buffered.Lifted
variable {α β : Type*} {N m L B: Side} {j:ℕ}{r:ℝ}
variable {S:ℕ→Side}{R:ℕ→ℝ}
-- use struct explicitly
structure Agenda (α:Type*) (R:ℕ→ℝ) where
  posV :α→ Gaia
  appointments :ℕ→α→ Cover
  timeR (i) : Tendsto (fun k:ℕ=> riseX (R k) (appointments k i)) atTop (𝓝 (posV i))
  tied :∀ i j,posV i=posV j→∀ᶠ k:ℕ in atTop, appointments k i=appointments k j
namespace Agenda
def plot (P:Agenda α R)(W:α→Wing) : Plot α R := ⟨P.appointments,W,P.posV,P.timeR,P.tied⟩
def part (P:Agenda α R)(f:β→α): Agenda β R:=⟨P.posV ∘ f,fun k i=> P.appointments k (f i),fun i=>P.timeR (f i),fun i j=>P.tied (f i) (f j)⟩
end Agenda
variable (M:ℕ→Jill.Male) (p:∀ i,Wave (Single (S i))) (e:Yard S R) (hj:1≤j)(g:∀ᶠ i in atTop,Sea (latPose j (M i) (S i)) (p i))
variable (P:Agenda α R) (Z:α→Personality)
local notation "L" i:max=> ledger (S i) j (M i)
local notation "PLAY" i:max k:max w:max=>player (S i) (P.appointments i k) (R i) w
open Personality
namespace PriceCliff
include e hj g
lemma plot_pay (A: Plot α R)(T:List α): Tendsto (fun i=>SpinPrice (p i) (rollC (ton ∘ (A.tag (m:=i) (0:Site (S i)) (Kea.tax emptyC) 1)) T)) atTop (𝓝 (Emu.runes A.rho T)):=by
 obtain ⟨r,hr,h⟩:= salutary j hj; let I(i):= (iceK j (too (S i)) (M i) r:ℂ); let A'(i):ℂ:= inner ℂ (mateK (S i)) (p i)
 have he : Tendsto (fun i=> Plot.stanza 1 (p i) (A.tag (m:=i) (0:Site (S i)) (Kea.tax emptyC) 1) T (runes A.rho T)/I i) atTop (𝓝 0):= A.hoot (fun _=>emptyC) (fun i=>too (S i)) M (fun _=>1) (fun _=>0) e p g hj hr T
 let a:= Emu.runes A.rho T
 have hv:= payM 1 he (g:=fun i=> I i/A' i) (g.mono fun i hi=>by unfold I A'; rw [norm_div, Complex.norm_real,Real.norm_of_nonneg (ice_p _ _ _ hr).le, on_voucher (e.even _) h hi, div_self (ice_p _ _ _ hr).ne']) -- tune
 apply ((show Tendsto _ atTop (𝓝 a) from zero_add a ▸ hv.add_const a)).congr'
 filter_upwards [g] with i y
 let d:= rollC (ton ∘ A.tag (m:=i) (0:Site (S i)) (Kea.tax emptyC) 1) T; let x:= inner ℂ (mateK (S i)) (acts d (p i)); let l:=A' i; unfold Plot.stanza pRead at *; rw [quant_one,mul_one,skyGlow,quant_one,act_one]; change I i/l*((x-l*a)/I i)+a=x/l; have hp: (I i)≠0:= Complex.ofReal_ne_zero.mpr (ice_p _ _ _ hr).ne'; have he:l≠0:= can_spend (e.even i) hj y; field_simp; ring
omit e hj g
-- rank operation on Hose, physical. Needs like sign-case. x.pose assigned next.
abbrev toward (x:Gaia)(t u:Personality):= if t.color=u.color then inner ℂ t.voice (acts (pencil x) u.voice) else 0
def poster (x y:Gaia) (t u:Personality):= if t.down=u.down then (0:ℂ) else if t.down then toward (x-y) t u else - toward (y-x) u t
lemma flip (x y:Gaia) (t u:Personality) : poster x y t u= -poster y x u t:=by cases h:t.down<;> cases p:u.down<;> simp [poster,h,p]
lemma rank_flip (M:Op (Single N)) (u v: Reader0 (Single N)): rankG M u v= -rankG M v u:=by unfold rankG; cases h:u.1 <;> cases p:v.1 <;> simp
lemma owing {b d:Bool}{s t:SpinIdx} {z z':Slot}{g:s∈payroll b}{h:t∈payroll d} (x:Gaia) : toward x (pureV b z s g) (pureV d z' t h)= Emu.frank ⟨s,z,1⟩ ⟨t,z',1⟩ x:=by simp [Emu.frank,toward,pureV]
include e hj g
lemma frontrunner (a b:α) (z z':Slot) {i l :SpinIdx} (hi:i∈payroll true) (hl:l∈payroll false):
    Tendsto (fun n=> rankG (L n) (PLAY n a (pureV true z i hi)) (PLAY n b (pureV false z' l hl))) atTop (𝓝 (toward (P.posV a-P.posV b) (pureV true z i hi) (pureV false z' l hl))):=by
 let C:Bool→α:=fun w=>if w then a else b
 let U:Bool→Personality:=fun w=>if w then pureV true z i hi else pureV false z' l hl
 let H:=(P.part C).plot (fun q:Bool=> if q then ⟨i,z,1⟩ else ⟨l,z',1⟩); let K(n):=H.tag (m:=n) (0:Site (S n)) (Kea.tax emptyC) 1; let Q(n:ℕ)(w:Bool):Reader0 (Single (S n)):=PLAY n (C w) (U w)
 have he : Tendsto (fun i=>SpinPrice (p i) (rollC (ton∘ K i) [true,false])) atTop (𝓝 (H.rho true false)) := (duo H.rho true false) ▸ plot_pay M p e hj g H [true,false]
 have ht1(n): K n true= PLAY n a (pureV true z i hi):= (player_pure ..).symm
 have ht2(n): K n false= PLAY n b (pureV false z' l hl):= (player_pure ..).symm
 let t:= pureV true z i hi; let u:=pureV false z' l hl
 have hg:H.rho true false=toward (P.posV a-P.posV b) t u:=by rw [Plot.rho]; change (if signW ⟨i,z,1⟩=signW ⟨l,z',1⟩ then 0 else if signW ⟨i,z,1⟩ then Emu.frank ⟨i,z,1⟩ ⟨l,z',1⟩ (P.posV a-P.posV b) else _) = _; simp only [t,u,down_here hi,down_here hl,Bool.true_eq_false,ite_false,ite_true]; exact (owing ..).symm
 rw [hg] at he; apply he.congr'; filter_upwards [g] with n w; rw [reckons (M n) (e.even n) hj w (K n) (fun j=>nac_k ..), duo, ht1,ht2]
-- Assemble full pair.
omit e hj g
private lemma doublet {I J :Type*} [Fintype I][DecidableEq I][Fintype J][DecidableEq J] (A:Op I)(F G:J→Ket I)(S T: Finset J)(f q:J→ℂ): inner ℂ (∑ i∈S,f i • F i) (acts A (∑ i∈T,q i • G i))= ∑ i∈S,∑ j∈T,(star (f i)*q j)*inner ℂ (F i) (acts A (G j)):= by
 rw [sum_inner]; apply sum_congr rfl; intro i _; rw [map_sum,inner_sum]; apply sum_congr rfl; intro j _; rw [map_smul,inner_smul_left,inner_smul_right]; exact (mul_assoc ..).symm
private lemma pureRank {x y:Personality}(w:x.down=true)(u:y.down=false)(A:Op (Single N))(a b:Cover): rankG A (player N a r x) (player N b r y) = inner ℂ (pitch N a r x.color x.voice) (acts A (pitch N b r y.color y.voice)):=by simp [player,w,u,rankG]
include e hj g
private lemma generalDown {x y:Personality}(w:x.down=true)(u:y.down=false)(a b:α): Tendsto (fun n=> rankG (L n) (PLAY n a x) (PLAY n b y)) atTop (𝓝 (toward (P.posV a-P.posV b) x y)):=by
 let Δ:= P.posV a-P.posV b; let U:= payroll x.down; let V:= payroll y.down; let f(i l:SpinIdx):= star (x.voice i)*y.voice l; let F(i l:SpinIdx)(n:ℕ):= inner ℂ (pitch (S n) (P.appointments n a) (R n) x.color (basisKet i)) (acts (L n) (pitch (S n) (P.appointments n b) (R n) y.color (basisKet l)))
 let G(i j:SpinIdx):ℂ:= if x.color=y.color then pencil Δ i j else 0
 have he(i l: SpinIdx)(p': i∈U)(q:l∈ V):Tendsto (F i l) atTop (𝓝 (G i l)):= by
    unfold U at p'; rw [w] at p'; unfold V at q; rw [u] at q
    have hp:=frontrunner M p e hj g P a b x.color y.color p' q; simp_rw [pureRank (x:=pureV true x.color i p') (y:=pureV false y.color l q) rfl rfl,owing] at hp; exact hp
 simp_rw [pureRank w u]
 have hz:toward Δ x y=∑ i∈U,∑ j∈V,f i j*G i j:=by
    unfold toward; split
    next he=> nth_rw 1 [←hymn x, ←hymn y]; rw [doublet]; simp [G,f,he,U,V]
    next ha=> simp [G,ha]
 change Tendsto _ _ (𝓝 (toward Δ x y)); rw [hz]; simp_rw [pitch_sum x,pitch_sum y,doublet]; exact tendsto_finsetSum _ fun i u'=>tendsto_finsetSum _ fun k w'=>(he i k u' w').const_mul _
lemma whole(x y:Personality) (a b:α): Tendsto (fun n=> rankG (L n) (PLAY n a x) (PLAY n b y)) atTop (𝓝 (poster (P.posV a) (P.posV b) x y)):= by
 by_cases h:x.down=y.down; · simp [h,poster,rankG,player]
 cases w:x.down
 · have u:y.down=true:=by revert h; rw [w]; cases y.down <;> simp
   simp_rw [rank_flip (L _) (player _ _ _ x), flip _ _ x y]
   refine Tendsto.neg (show Tendsto _ _ _ from ?_)
   rw [poster]; simp only [w,u,Bool.true_eq_false,ite_true,ite_false]; exact generalDown M p e hj g P u w ..
 have u:y.down=false:=by revert h; rw [w]; cases y.down <;> simp
 rw [poster]; simp only [w,u,Bool.true_eq_false,ite_true,ite_false]; exact generalDown M p e hj g P w u ..
noncomputable def quantum (X:α→Gaia)(Z:α→Personality) (T:List α):= Emu.runes (fun a b=> poster (X a) (X b) (Z a) (Z b)) T
noncomputable def literal (X:α→ Cover)(Z:α→Personality)(N:Side)(R:ℝ)(T:List α): FC (Single N):= rollC (fun i=>ton (player N (X i) R (Z i))) T
lemma wordPrice (T:List α): Tendsto (fun i=>SpinPrice (p i) (literal (P.appointments i) Z (S i) (R i) T)) atTop (𝓝 (quantum P.posV Z T)):=by
 refine (offer_v (fun a b=>poster (P.posV a) (P.posV b) (Z a) (Z b)) (fun n a b=> rankG (L n) (PLAY n a (Z a)) (PLAY n b (Z b))) (fun i j=>whole M p e hj g P (Z i) (Z j) i j) T).congr' ?_
 exact g.mono fun i v=>(reckons (M i) (e.even i) hj v (fun s=> player (S i) (P.appointments i s) (R i) (Z s)) (fun s=> player_tones ..) T).symm
end PriceCliff
end YM.CF.Hygrometry
