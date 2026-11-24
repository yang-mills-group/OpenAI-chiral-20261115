import YM.SU5.FiniteGaugeData.Signal.LocalWork
import YM.SU5.FiniteGaugeData.Reliance.Candela
import YM.SU5.FiniteGaugeData.Signal.RoofTariff
/-! # Within-volume replication uses the physical warm signed state of the ticket.
Numerator estimate after occupation suppression. Carry NON-tag marks only. Expense uses
M2 copies actually present on the torus. We specialize only after defining the growth. -/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Advance Reef Hom Tenant Branch
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Supplies Invest Momentum Furnace
namespace Kinetic
variable {N:Side}{T:Support (More N)}{i j k d:ℕ}{a b C H u v e:ℝ}
-- noop

def Booted (j:ℕ)(X:GramM N)(S:Loom N)(c H:ℝ)(s:Support (More N))(n:ℕ)(f:Mark N):=
    ∀ᵐ v∂city N, f (drawn S v) = 0 ∨ Furnace.Vine.riveted (spar j X.J.M (S v)) (Momentum.pullP j X.J.P X.J.M (S v)) H c (modesIn N s) (Tset N) n (f (drawn S v))
section geometry
variable {X:GramM N}{S:Loom N}{f x:Mark N}
lemma boots_merge (p:Booted j X S a H T k x) (g:AtSupport false T x){A:Support (More N)}(h:Booted j X S a H A d f)(v: AtSupport false A f) (e:Disjoint T A): Booted j X S a H (T∪A) (k+d) (x*f):=by
 filter_upwards [p,h] with i a c; rcases a with t|t; · left; rw [Pi.mul_apply,t,zero_mul]
 rcases c with u|u; · left; rw [Pi.mul_apply,u,mul_zero]
 right; rw [Pi.mul_apply]; let z:=drawn S i
 have hx:Disjoint (modesIn N T) (modesIn N A):= Finset.disjoint_left.mpr (fun i p q=> Finset.disjoint_left.mp e ((modes_at _ _).mp p) ((modes_at _ _).mp q))
 apply Furnace.Vine.grow (Furnace.Vine.addOn t u hx (g.allV z).sector (v.allV z).sector); exact union_subset (modes_monotone subset_union_left) (modes_monotone subset_union_right)
variable {B L:Side}{h': Odd L.val}{Y:Pricing j L h' (Thread j)}{P:Grasp Y B e}
variable (l:Credit)(F:InterestX l N X.J)(R: P.roundZ ≤ N.val)
variable (w:Roof N v e i S) (p0:1≤j)(K:Stamped j L h' Y)
include F R w p0 K
lemma boots_reflection (t:Booted j X S a H T k x) (z:ℤ)(n:Axis)(p:0<H): Booted j X S a H (T.image ((plane n z).anon N)) k (reflMark n z x):=by
 let Y':= plane n z; let W:= fling n z N; let U:= carR n z N
 filter_upwards [(reflOrbit_mp n z).quasiMeasurePreserving.ae t, roof_move (i:=n) (s:=z) S w] with i h v -- parameters tune
 let y:=S (reflOrbit n z N i); have he:S i=W y:=by
    have hy:y=W (S i):= congrArg Prod.snd v; rw [hy, show W (W (S i))= _ from fling_invol n z _]
 simp only [reflMark,←v]; rcases h with h|h; · left; rw [h, theta_zero]
 right; have q': Guard y e:= w.paid _; let Z:=spar j X.J.M y; let Z':= spar j X.J.M (S i)
 let L:=pullP j X.J.P X.J.M y; let L':=pullP j X.J.P X.J.M (S i)
 have q:= ornaments R X.J.P X.J.M y q' K p0 F.leanJ.1 F.ready z n
 exact Furnace.Vine.reflectSegments (pillar R _ _ q') (refuge R _ _ _ q') p h U (exchanges_halves n z N) (refl_modes n z T) (show twist U Z=1-Z' from (by unfold Z'; rw [he]; exact q.1)) (show L'= _ from (by unfold L'; rw [he]; exact q.2.1)) (pillar R _ _ (w.paid i)) (refuge R _ _ _ (w.paid i))
end geometry
open Graph Precision YM.Next.Rank Girt PathData Py Afterglow Vale.Grace
section funds
variable {m B L:Side}{h': Odd L.val}{Y:Pricing j L h' (Thread j)}{P:Grasp Y B e}
local notation "Λ"=> Scree.mid m B
local notation "M"=> More (Scree.mid m B)
variable {h v' b0 μ C' γ L' A' z r s:ℝ}
variable {X:GramM (mid m B)}{S:Loom (mid m B)}
variable (G: Roof (mid m B) z e k S)(R:P.roundZ ≤ (mid m B).val)
variable (W: Graph.Ledger h v' b r C X)(hr:0 ≤ r)(hp:0≤ C)(p:1 ≤ H)(w:H ≤ h)(O:HaarBudget group){g:ℝ}(t:X.path.Bounds X.funds μ γ L')(q:0<g)(vq:X.beta*g^2=1)(d':g ≤ X.p.threshold)
local notation "B'"=> flagBill Λ v' b C
local notation "J"=> taxY M X.beta X.p.threshold γ L' + Fintype.card (Face (Per M))/2
include G W R hr hp p w
lemma value (f: Buffered.Mark Λ)(S':Support M)(u:Booted j X S a H S' d f)(h0:0≤a): ∀ᵐ z∂city Λ,‖letterRead (f (drawn S z)) (recX P X S z)‖ ≤ Graph.past X z.1*Real.exp (flagBill Λ v' b C)*a^d:= by
 have hx: 0 < H:=zero_lt_one.trans_le p; have hh:0≤h:=hx.le.trans w; let Q:=a^d; have hq:0≤Q:= pow_nonneg h0 _
 filter_upwards [u] with z l; let Ξ:= Graph.past X z.1
 rcases l with l|l; · rw [l]; change ‖inner ℂ (mateK Λ) (acts 0 _)‖ ≤ _; simp only [act_zero,inner_zero_right,norm_zero]; have hΞ:0≤Ξ:= (Real.exp_pos _).le; exact mul_nonneg (mul_nonneg hΞ (Real.exp_pos _).le) hq
 let y:= S z; let A:= spar j X.J.M y; let p':= pillar (Y:=Y) R X.J.M y (G.paid _); let s:=mateK Λ; let Y':= changeM P y X.J.M; let U:=actF j X S z; let M':= exp (dg U); let x:= f (drawn S z)
 let D:= actG X z; let V:= fueled X.p X.K z; let f':=‖inner ℂ s (acts x (acts (tank A (X.board z)*M') Y'))‖
 have hp2:= thermalCap X S W z hr j p' (show (0:ℝ) ≤ 2 by norm_num) (railT _ r hr); have hp3:x=x:=rfl
 let u:=pittance Λ 2 C; let z':=doorF Λ 2 C; let k':=(v'+v')*((M).val:ℝ)^4; let v₀:= b*((M).val:ℝ)^4
 have hv : f' ≤ Real.exp z'*Real.exp k' * Real.exp v₀ *Q := by
    apply (Furnace.Vine.burn_ten p' (p:=hx) (q:=Momentum.refuge R _ _ _ (G.paid z)) (g:=l) (l:=sea_g R y (G.paid z) X.J.M) (w:=touchP Λ ▸ tickB Λ) p w D V h0).trans -- args ambiguous
    apply mul_le_mul_of_nonneg_right _ hq
    refine mul_le_mul (mul_le_mul ((Graph.bootC _).trans (Real.exp_le_exp.mpr hp2)) (Real.exp_le_exp.mpr (marks X z W.reg W.slip hh)) (Real.exp_pos _).le (Real.exp_pos _).le) (toeF W.force hh z) (Pastry.pitch hh _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
 rw [Graph.porch,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul ]; unfold Graph.beam Graph.mile; rw [act_smul,map_smul, norm_smul,norm_smul]; change ‖((Ξ:ℂ))‖*(‖Complex.exp (-Pec.pigment X.J.I y)‖*f') ≤ _; rw [Complex.norm_real,Real.norm_of_nonneg (show 0≤Ξ from (Real.exp_pos _).le)]
 let y0:=-Pec.pigment X.J.I y; have hb : ‖Complex.exp y0‖ ≤ Real.exp u:=(Complex.norm_exp_le_exp_norm y0).trans (Real.exp_le_exp.mpr (by unfold y0; rw [norm_neg]; exact aurP _ _ W.field.2 (railT _ _ hr) (by norm_num)))
 rw [mul_assoc _ (Real.exp _)]; apply mul_le_mul_of_nonneg_left ?_ (show 0 ≤ Ξ from (Real.exp_pos _).le); exact (mul_le_mul hb hv (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by unfold Q; rw [flagBill,←Real.exp_add,←Real.exp_add,←mul_assoc,←Real.exp_add]; unfold v₀ z' u k'; ring_nf)
include t q vq d'
theorem charge (f: Buffered.Mark Λ)(S':Support M)(u:Booted j X S a H S' d f)(h0:0≤a):
    ‖num0 P X S f‖ ≤ a^d * (Real.exp (flagBill Λ v' b C +(Fintype.card (Face (Per M)):ℝ)/2) * fullRate O X γ L' g):=by
 let L(z:Orbit Λ):= Real.exp (-basal X g z.1); let Θ:=Real.exp (B'+ (taxY M X.beta X.p.threshold γ L'+ Fintype.card (Face (Per M))/2))
 obtain ⟨p',U⟩:=repays O X q; let Q:=a^d; have hQ:0≤Q:=pow_nonneg h0 _
 unfold num0 markedRead; apply (norm_integral_le_integral_norm ..).trans; refine le_trans (integral_mono_of_nonneg (Eventually.of_forall (fun _=>norm_nonneg _)) (g:=fun i:Orbit Λ => (Q * Θ)*L i) (p'.const_mul _) ?_) ?_; swap
 · rw [integral_const_mul]; refine (mul_le_mul_of_nonneg_left U (mul_nonneg hQ (Real.exp_pos _).le)).trans ?_; rw [fullRate, mul_assoc]; apply mul_le_mul_of_nonneg_left _ hQ; rw [←mul_assoc (Real.exp _),←Real.exp_add]; apply mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (by unfold Window.rebate; have he:=strength_pos X.funds; have hl:=zero_lt_one.trans_le O.big_ge; positivity) -- tune
   linarith only [Nat.cast_nonneg (α:=ℝ) (Fintype.card (Face (Per M)))]
 filter_upwards [value G R W hr hp p w f S' u h0] with z y
 have ht:= past_budget X t q vq d' z.1 (w:=0) le_rfl (Or.inr rfl) (Or.inr rfl)
 simp only [zero_mul,mul_zero,zero_div,sub_zero] at ht
 apply y.trans; unfold Θ; rw [Real.exp_add]; unfold Q; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le) hQ).trans_eq; ring
end funds
end Kinetic
end YM.CF.Signal
#print axioms YM.CF.Signal.Kinetic.charge
