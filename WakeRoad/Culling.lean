import WakeRoad.Lumber
/-! # Oriented comparisons and deck legality. -/
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 25000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Buffered Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Skye Precision Tree Fock
attribute [local instance] opCStarAlgebra
open PhysicalNext.JointLoad.Heir
open YM.WakeRoad CF.Pannier.Chancel Rous Pressure Papal EmberWind Work.E08
open Gleam Regis Regis.Head Gleam.Wake
open CF.Gingham.Ruff
local notation "G₅"=> SU.group
open CF.Gingham.Ruff
namespace ArborJet
variable {N:Side}{m d s:ℕ}{S:Support (More N)}
local notation "M"=> Signed.mirror (3:Axis)
open Afterglow Journey Tapestry CF.WakeInvestment Vale
open Lamour.Bridge Celeste Clock Hookah
open Regis.Wake
open scoped ContDiff

variable {J:Type}[Fintype J][DecidableEq J]
abbrev planter (V:Bool→Vessel SU.group (More N) J):Vessel SU.group (More N) (Bool×J):=⟨fun i=>(V i.1).view i.2⟩
abbrev brushpot(R:Bool→WakeRoad.Press J)(x:Bool×J→ℝ):ℂ:= WakeRoad.Score (R false) (fun i=>x (false,i))*WakeRoad.Score (R true) (fun i=>x (true,i))
variable (R:Bool→WakeRoad.Press J)
local notation "c!" i:max=> WakeRoad.coin (R i)
private lemma price_points (x:Bool × J→ℝ)(b:Bool): ‖fun i:J=>x (b,i)‖ ≤ ‖x‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun _=> norm_le_pi_norm ..
lemma brush_fine (C:ℝ)(h₀:0≤C)(p:∀i,2* WakeRoad.coin (R i) ≤ C): Paint (brushpot R) 4 (2*C^2):=by
 refine ⟨(show ContDiff ℝ 1 _ from by unfold brushpot WakeRoad.Score; fun_prop),?_,?_⟩
 · intro a ha v t; let Y(b):= WakeRoad.Score (R b) (fun i=> v (b,i)); rw [show brushpot R v=Y false*Y true from rfl,norm_mul]
   have h(i:Bool):‖Y i‖ ≤ C*a^2:= ((score_sol _).worth _ ha _ ((price_points v i).trans t)).trans (mul_le_mul_of_nonneg_right (p i) (sq_nonneg _)); exact (mul_le_mul (h _) (h _) (norm_nonneg _) (mul_nonneg h₀ (sq_nonneg a))).trans (by have he:0≤a:=zero_le_one.trans ha; rw [show C*a^2*(C*a^2)= C^2*a^4 by ring]; gcongr; linarith [sq_nonneg C])
 intro a ha v v' p₁ p₂; let X(v:Bool × J →ℝ)(b:Bool):= WakeRoad.Score (R b) (fun i=> v (b,i))
 change ‖X v false*X v true-X v' false * X v' true‖ ≤_
 have h(v:Bool × J→ ℝ)(g:‖v‖ ≤ a)(b:Bool): ‖X v b‖ ≤ C*a^2:= ((score_sol _).worth _ ha _ ((price_points v b).trans g)).trans (mul_le_mul_of_nonneg_right (p _) (sq_nonneg _))
 have t(i:Bool): ‖X v i-X v' i‖ ≤ C*a^2*‖v-v'‖:= ((score_sol _).price _ ha _ _ ((price_points v i).trans p₁) ((price_points v' i).trans p₂)).trans (mul_le_mul (mul_le_mul_of_nonneg_right (p i) (sq_nonneg _)) (price_points (v-v') i) (norm_nonneg _) (mul_nonneg h₀ (sq_nonneg a)))
 rw [show X v false*X v true-X v' false*X v' true=(X v false-X v' false)*X v true+X v' false*(X v true-X v' true) from by ring]
 apply (norm_add_le ..).trans; simp only [norm_mul]; have v:0≤C*a^2:=mul_nonneg h₀ (sq_nonneg _); refine (add_le_add (mul_le_mul (t _) (h _ p₁ _) (norm_nonneg _) (mul_nonneg v (norm_nonneg _))) (mul_le_mul (h _ p₂ _) (t _) (norm_nonneg _) v)).trans_eq ?_; ring
lemma paint_more {k:ℕ}{c d:ℝ}{F:(J→ℝ)→ℂ}(p:Paint F k c)(e:c≤d):Paint F k d:= ⟨p.bright,fun s t g u=>(p.worth s t g u).trans (mul_le_mul_of_nonneg_right e (pow_nonneg (zero_le_one.trans t) _)),fun K h f g u v=>(p.price K h f g u v).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e (pow_nonneg (zero_le_one.trans h) _)) (norm_nonneg _))⟩

-- legal plantation K (compass.P.E pre vote)
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))(s i k:ℕ)
local notation "Ω"=>side Y i s
local notation "▷"=>RootBook Y i k s
variable {A C ρ:ℝ}{e:ℕ}{o: Skye.Seat (side Y i s)}
local notation "B*"=>BlockP e o
structure RowBook {q:Support (More (side Y i s))}{J:Type}[Fintype J](e r' z ρ:ℝ)(d:ℕ)(W:Mark (side Y i s))(V:Vessel SU.group (More (side Y i s)) J)(C:WakeRoad.Press J):Prop where
 active: AtSupport false q W
 pure: covariant W
 rounded : V.Ship q d
 score_tab: 2 * WakeRoad.coin C ≤ e
 income : ∃ ψ:Pane (side Y i s)→ℂ, Envelope ψ ∧ (∀ x:Fields _,W x=ψ x.1 • 1)∧ GaugeInvariant ψ∧(∀u,‖ψ u‖≤ r')∧
    ∀ U:Pane _,WellDrawn Y s i k (1/2) q U → ‖ψ U-WakeRoad.Score C (V.material ρ U)‖ ≤ z
local notation "#ₙ"=>radiusB (hat P.R.L P.x s)
lemma pruning {W:Bool→Mark (side Y i s)} {V:Bool→Vessel SU.group (More (side Y i s)) J} {c₀ r' z:ℝ}
    (L:∀ b:Bool,RowBook Y s i k (q:=BlockP e o) c₀ r' z ρ (#ₙ) (W b) (V b) (R b))
    (v:0≤r')(v':0 ≤ z)(t:0≤c₀)
    (p₁:(↑(Fintype.card (Bool×J)):ℝ) ≤ sPow P s A)
    (p₂:2*c₀^2 ≤ sPow P s A)
    (p₃:r' *r' ≤ sPow P s A)
    (p₄:(↑(2*e:ℕ):ℝ) ≤ sPow P s A)
    (pq:(↑(BlockP e o).card:ℝ) ≤ sPow P s A)
    (p₅:|ρ| ≤ 2*bornQ P s)
    (pv:z*(2*r'+z) ≤ scratch (hat P.R.L P.x s)) :
  Broom Y s i k (planter V) A (1/2) ρ (2*e) 0 4 (Jewel.landQ _ (W false*W true) o e) (brushpot R):= by
 choose ψ env ψW g cash book using fun b=> (L b).income
 have W₂(x): (W false*W true) x = ((ψ false*ψ true) x.1) • 1:=by rw [Pi.mul_apply,ψW,ψW, Matrix.smul_mul, Matrix.mul_smul,one_mul,smul_smul];rfl
 have rent(x): ‖(ψ false*ψ true) x‖≤ r'*r':=by rw [Pi.mul_apply,norm_mul];exact mul_le_mul (cash ..) (cash ..) (norm_nonneg _) v
 refine ⟨ (L false).active.mulM (L true).active,fun x y=> ?_, fun x=> ?_,(fun i=>blocks_rest o e i),p₄,pq,(ψ false*ψ true),?_,?_⟩
 · let X(b:Bool):= (L b).pure x y;change (W false _*W true _)=_; rw [X false,X true]; symm; exact map_mul _ _ _
 · change Cadre _ 0 _ ((W false*_) x); rw [W₂]; exact (Cadre.unit.scale _).buy le_rfl ((mul_one _).le.trans ((rent _).trans p₃))
 · refine ⟨⟨fun i=>(L i.1).rounded.lives i.2,fun i=>(L i.1).rounded.keeps i.2,fun i=>(L i.1).rounded.pay i.2⟩,paint_more (brush_fine R c₀ t (fun i=>(L i).score_tab)) p₂,p₁,(by norm_num),p₅,⟨(env false).meas.mul (env true).meas,_,rent⟩, fun a U=>congrArg₂ (·*·) (g false _ _) (g true _ _),fun i=>(rent i).trans p₃,fun x h=>?_⟩ -- Paint.mono?
   let Y₁(i:Bool):= WakeRoad.Score (R i) ((V i).material ρ x)
   have ht(i):‖ψ i x - Y₁ i‖ ≤ z:= book i x h
   let P₁(i:Bool):= ψ i x
   have q(i): ‖Y₁ i‖ ≤ r' + z:=by have e:=norm_sub_norm_le (Y₁ i) (ψ i x); rw [norm_sub_rev] at e; linarith only [e,ht i,cash i x]
   change ‖P₁ false*P₁ true - Y₁ false*Y₁ true‖≤_
   rw [show P₁ false*P₁ true-Y₁ false*Y₁ true=P₁ false*(P₁ true-Y₁ true)+(P₁ false-Y₁ false)*Y₁ true from by ring]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]; refine (add_le_add (mul_le_mul (cash ..) (ht true) (norm_nonneg _) v) (mul_le_mul (ht false) (q true) (norm_nonneg _) v')).trans ?_; exact pv.trans' (le_of_eq (by ring))
 intro x _; change ‖noble Y s i k ((W false*_) x)-_‖≤ _; rw [W₂,noble_linear,map_smul,←noble_linear,noble_unit, smul_eq_mul,mul_one,sub_self,norm_zero];exact (chip_pos ..).le
#print axioms pruning
lemma plants {W: Mark (side Y i s)}{R:WakeRoad.Press J}{V:Vessel SU.group (More (side Y i s)) J} {c₀ r' z:ℝ}
   (L:RowBook Y s i k (q:=BlockP e o) c₀ r' z ρ (#ₙ) W V R)
   (h:1≤c₀)(u:1≤r')(t:0≤z)
    (p₁:(↑(Fintype.card (Bool×J)):ℝ) ≤ sPow P s A)
    (p₂:2*c₀^2 ≤ sPow P s A)
    (p₃:r' *r' ≤ sPow P s A)
    (p₄:(↑(2*e:ℕ):ℝ) ≤ sPow P s A)
    (pq:(↑(BlockP e o).card:ℝ) ≤ sPow P s A)
    (p₅:|ρ| ≤ 2*bornQ P s)
    (pv:z*(2*r'+z) ≤ scratch (hat P.R.L P.x s)):
  Broom Y s i k V A (1/2) ρ (2*e) 0 2 (Jewel.landQ _ W o e) (WakeRoad.Score R):=by
 obtain ⟨ψ,env,hp,g,price,accuracy⟩:=L.income;have ht (i): ‖ψ i‖ ≤ sPow P s A:= (price i).trans (p₃.trans' (by nlinarith only [u,(sq_nonneg (r'-1))]))
 refine ⟨L.active,L.pure,fun x=>?_,fun i=>blocks_rest ..,p₄,pq,ψ,⟨L.rounded,paint_more (score_sol _) (L.score_tab.trans (by nlinarith only [p₂,sq_nonneg (c₀-1),h])),p₁.trans' ?_,by norm_num,p₅,env,g,ht,fun x w=> (accuracy x w).trans (pv.trans' ?_)⟩,fun x _=>?_⟩
 · change Cadre _ 0 _ (W x); rw [hp]; exact Cadre.unit.scale _ |>.buy le_rfl (by rw [mul_one]; exact ht _)
 · simp only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]; have := Nat.cast_nonneg (α:=ℝ) (Fintype.card J); linarith
 · exact le_mul_of_one_le_right t (by linarith)
 change ‖noble Y s i k (W x)-ψ x.1‖≤_; rw [hp,noble_linear,map_smul,←noble_linear,noble_unit, smul_eq_mul,mul_one,sub_self,norm_zero];exact (chip_pos ..).le

#print axioms plants
