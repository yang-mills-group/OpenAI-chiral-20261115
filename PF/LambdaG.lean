import PF.Pigment
set_option autoImplicit false
set_option maxHeartbeats 90000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
namespace PureForce.LambdaG
open Pec Push.AbsoluteSums -- Walrus?
variable {n:Side}
local notation "G"=>SU.group
local notation "W" n=>More n
-- threshold earns reel. chord global diameter + exp continuity. ℰp uses β', separate β_R
open Pressure
private def decay (β:ℝ):= ((Real.sqrt β)⁻¹)^(1/8:ℝ)
private def swell (y:ℝ):= Real.exp (Real.log (Real.log y)^ (2:ℕ))
private lemma epsDec {β:ℝ} (h:0<β):rotorEps β = (Real.sqrt β)⁻¹ * decay β:=by rw [rotorEps,Real.rpow_add (inv_pos.mpr (Real.sqrt_pos.mpr h)),Real.rpow_one]; rfl
private lemma epsFund {β X:ℝ}(hx:2≤X)(g:X/2≤β): rotorEps β≤1 ∧ rotorEps β ≤ (2*(Real.sqrt X)⁻¹)*decay β:=by
  have hb:1≤β:=by linarith
  have hv:0<β:=by linarith
  have ht:= Real.sqrt_pos.mpr hv; have hX:0<X:=by linarith
  have hh : 1 ≤ Real.sqrt β := by nlinarith [Real.sq_sqrt hv.le]
  have hu:(Real.sqrt β)⁻¹ ≤ 1:= (inv_le_one₀ ht).mpr hh
  rw [epsDec hv]; have he:0 < decay β:= Real.rpow_pos_of_pos (inv_pos.mpr ht) _
  constructor
  · exact (mul_le_one₀ hu he.le (show decay β ≤ 1 from Real.rpow_le_one (inv_pos.mpr ht).le hu (by norm_num))) -- syntax lemma orientation?
  apply mul_le_mul_of_nonneg_right ?_ he.le
  have hi:= Real.sqrt_pos.mpr hX
  field_simp; nlinarith only [ht,hi,Real.sq_sqrt hv.le,Real.sq_sqrt hX.le,g,hX]
-- uniform angular-linear purchase, separately use smallRotor for old χ
private lemma chartRotor : ∃ D:ℝ,0<D ∧ ∀ᶠ X:ℝ in atTop,∀ β:ℝ,X/2≤β → ∀ m:ℝ,|m|≤24 →∀ ξ:SU.group.Color, ‖ξ‖ ≤ 1 →∀ b:Bool,
    SU.group.chord (rotorLeft b m β ξ) + SU.group.chord (rotorRight b m β ξ) ≤ D* rotorEps β ∧
    SU.group.chord (rotorLeft b m β ξ) + SU.group.chord (rotorRight b m β ξ) ≤ temp X/24:=by
  obtain ⟨C,δ,hC,hδ,hp⟩:= Next.Fluctuations.chord_chart_cost SU.group
  -- if ≥δ use all-group to avoid convergence lemma. linear global.
  let D:ℝ:=C+2/δ; have hh:0<D:=by unfold D; positivity
  refine ⟨24*D,by positivity,?_⟩
  filter_upwards [smallRotor] with X h β ht m hm ξ hξ b
  have hb:0<β:=(half_pos h.1).trans_le ht
  have he:0 ≤ rotorEps β:= by unfold rotorEps; positivity
  let z:=(m*rotorEps β) • ξ
  have hi:‖z‖ ≤ 24*rotorEps β:=by unfold z; rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg he]; exact (mul_le_of_le_one_right (by positivity) hξ).trans (mul_le_mul_of_nonneg_right hm he)
  have hu: SU.group.chord (rotorElem m β ξ) ≤ D * ‖z‖:=by
    by_cases hr:‖z‖ ≤ δ
    · exact (hp z hr).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (norm_nonneg _))
    have hg: 2 ≤ (2/δ)*‖z‖:=(le_div_iff₀ hδ).mpr (show 2*δ≤2*‖z‖ by linarith) |>.trans_eq (by ring) -- div_mul?
    exact (SU.group.chord_le_two _).trans (hg.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC.le) (norm_nonneg _)))
  have h':=(h.2 β ht ξ hξ m hm)
  have hc:= hu.trans ((mul_le_mul_of_nonneg_left hi hh.le).trans_eq (show D*(24*rotorEps β)=24*D*rotorEps β by ring))
  cases b <;> simpa [rotorLeft,rotorRight,rotorElem] using (And.intro hc h')
abbrev Receipt (n:Side) := GP.Book (W n) ⊕ Boots.Doc n
-- U and V profiles before/after lie shift (one j when used on schedule): y and z Loom values
open Graph
namespace Receipt
variable (R:GramM n)
def length (d:Receipt n) := d.elim (fun i=> GP.offset (W n) R.path i) (fun i=> i.2.length) -- type infer
-- length of pigment individual shouldn't depend R

def expense (U V y z:Pane n)(i:Receipt n):ℂ := i.elim (fun i=> GP.chip (W n) R.path R.funds R.p R.beta U V i) (fun i=> Boots.Doc.chip R.J.I y z i)
-- implicit cast real inferred for left? lean

def wing (i:Receipt n):Support (W n) := i.elim (fun i=> GP.estate (W n) R.path i) (fun i=> Boots.lands i.1 i.2)
lemma profit {e:gaugeLink n}{U V y z:Pane n}{δ σ K L a C:ℝ}(T: GP.Toggle e R.p.threshold δ U V)(E:∀ i≠e,z i=y i)(F:∀ i,BPress.chord (z i) (y i)≤δ)
    (h:R.path.Bounds R.funds σ K L)(w:12 ≤ R.funds.relaxation * σ)(v:1≤R.beta)(p:0<a)(b:Lac R.J.I a C) :
    let c:= min (GP.Arm.Rate σ) (Boots.rate a);
    HasSum (expense R U V y z) ((R.path.inChannels R.funds R.p R.beta U-R.path.inChannels R.funds R.p R.beta V:ℝ)+ (Pec.pigment R.J.I y-Pec.pigment R.J.I z)) ∧
    SumBudget (fun i:Receipt n=> ‖expense R U V y z i‖*Real.exp (c*(length R i:ℝ))) (GP.guaranteed R.funds σ K L * R.beta* R.p.threshold*δ + Boots.collation a C *δ):=by
  intro c; obtain ⟨Q,f⟩:= GP.LPSeven h w _ T v
  have hb := Boots.batches R.J.I p b E F
  refine ⟨?_,Extra.Iteration.Cost.sum ?_ ?_⟩
  · have he:= Complex.hasSum_ofReal.mpr Q -- signature?
    have hx:= hasSum_fintype (Boots.Doc.chip R.J.I y z); rw [Boots.assemble] at hx
    exact HasSum.sum he hx -- ???
  · refine budget_mono f (fun _=> by positivity) ?_; intro i
    change ‖(↑(GP.chip (W n) R.path R.funds R.p R.beta U V i):ℂ)‖* _ ≤ _; rw [Complex.norm_real, Real.norm_eq_abs]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); apply Real.exp_monotone; change c * (GP.offset _ _ _:ℝ) ≤ _; exact mul_le_mul_of_nonneg_right (min_le_left ..) (Nat.cast_nonneg _)
  refine budget_mono hb (fun _=> by positivity) fun i=>?_ ; change ‖Boots.Doc.chip R.J.I y z i‖ * _ ≤ _; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply Real.exp_monotone; change c * (i.2.length:ℝ) ≤ _; exact mul_le_mul_of_nonneg_right (min_le_right ..) (Nat.cast_nonneg _)
lemma orientation (d:Receipt n){e:gaugeLink n}{U V y z:Pane n}{δ:ℝ}(T: GP.Toggle e R.p.threshold δ U V)(E:∀ i≠e,z i=y i) :
    Branch.Grove (BPress.Grid.field 4 (W n)) (d.wing R) ∧ (d.wing R).card ≤ d.length R ∧
    (expense R U V y z d≠0 → e.1∈d.wing R∧ e.1+step e.2∈d.wing R):=by
  cases d with
  | inl i => obtain ⟨_,a,_,b,d⟩:= GP.orientation (R:=R.path) (c:=R.funds) i T R.beta; exact ⟨a,b,fun v=>d (fun t=>v (by unfold expense; simp only [Sum.elim_inl,t,Complex.ofReal_zero]))⟩
  | inr i=> obtain ⟨_,a,_,b⟩:= Boots.flower i.2 i.1; exact ⟨a,b,Boots.touch R.J.I i E⟩
-- across spoiler with Γ(t) changed but flag landscape same at τ and kept base,
-- uses same supplies throughout even if W outside.
lemma economies (d:Receipt n){U V y z U' V' y' z':Pane n}(x:Agrees (d.wing R) U U')(w:Agrees (d.wing R) V V')
    (k:Agrees (d.wing R) y y')(j:Agrees (d.wing R) z z')(H:∀ t:Signed,GP.Rules R.funds R.p U U' t)(G':∀ t:Signed,GP.Rules R.funds R.p V V' t):
    d.expense R U V y z=d.expense R U' V' y' z':=by
  cases d with
  | inl i => change (↑(GP.chip (W n) R.path R.funds R.p R.beta U V i):ℂ)=(↑(GP.chip (W n) R.path R.funds R.p R.beta U' V' i):ℂ); exact congrArg (fun r:ℝ=> (r:ℂ)) (GP.prices (R:=R.path) i x w (H _) (G' _))
  | inr i=> unfold expense Boots.Doc.chip; dsimp only [Sum.elim_inr]; simp_rw [Boots.pearl_local R.J.I i.1 i.2 y y' k,Boots.pearl_local R.J.I i.1 i.2 z z' j]
end Receipt
-- standing choices pre-production. Include radius r tests and Loom condition, arbitrary inputs on current background at any toggle with post gate.
variable (P: Spine)
local notation "Λ" => P.par
local notation "Y0" => P.run
local notation "X(" s ")"=> hat P.par.R.L P.par.x s
local notation "rate0"=> min (GP.Arm.Rate P.par.K.top.width) (Boots.rate (levelQ P.par.W.C))
private lemma swipe {τ:ℝ}(_:0≤τ) (e:gaugeLink n)(b c:SU.E)(U:Pane n)
    (_:SU.group.chord b+ SU.group.chord c≤τ/24) {r:ℕ}(q: clean (τ/3) (rotorWindow r e) (oneOffer e b c U)) : ∀ p:Face (Per (W n)),e.1∈touched p → SU.group.chord (faceValue (oneOffer e b c U) p)<τ/3:=fun _ f=> q _ _ (by simp [rotorWindow,halo_spec]) f
private lemma toggleUp {τ δ:ℝ}(t:0≤τ) (e:gaugeLink n)(b c:SU.E)(U:Pane n)(h:SU.group.chord b + SU.group.chord c ≤ δ)
    (g:SU.group.chord b+ SU.group.chord c≤τ/24) {r:ℕ}(q: clean (τ/3) (rotorWindow r e) (oneOffer e b c U)) : GP.Toggle e τ δ U (oneOffer e b c U):=by
  have hl:= flags_stick b c t U g (swipe t e b c U g q)
  exact ⟨fun i hg=>one_off b c hg U,fun i=>(one_cost b c U i).trans h,fun _ _=> hl.2 _,fun p hp=> (hl.1 p hp).le.trans (half_le_self t)⟩

variable (C₁:ℝ)
local notation "C_g" => GP.guaranteed P.par.K.top.clip P.par.K.top.width P.par.K.top.paths P.par.V.W.bar
local notation "A_p"=>levelQ P.par.W.C
local notation "B_p"=>cashU P.par.W.C
local notation "C_p" => Boots.collation A_p B_p
def number:= |C_g| * 4*C₁+ |C_p| * 2*C₁+1
variable {P C₁}
-- elementary factor payout
private lemma received (T:GramM n){s:ℕ}{β':ℝ} (hX:2 ≤ X(s))(e:T.p=(Y0).meter.a s)(f:T.funds=(Λ).K.top.clip)
    (g:matchedX X(s) T.beta)(v:matchedX X(s) β')(p:0 < C₁):
    let δ:=C₁*rotorEps β'; GP.guaranteed T.funds (Λ).K.top.width (Λ).K.top.paths (Λ).V.W.bar*T.beta*T.p.threshold*δ + C_p*δ ≤ number P C₁*(((Real.sqrt β')⁻¹)^(1/8:ℝ))*Real.exp (Real.log (Real.log X(s))^(2:ℕ)):=by
  intro δ; rw [e,f,(Y0).meter.boot s|>.1]
  have ht':1≤β':=(by linarith only [hX,v.1]); have ht:=zero_lt_one.trans_le ht'; have hx:0<X(s):=by linarith
  have hr: 0≤decay β':= Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
  have hδ:0 ≤ δ:=by unfold δ rotorEps; positivity
  let F:=Real.exp (Real.log (Real.log X(s))^(2:ℕ)); have hl:1≤F:= Real.one_le_exp (sq_nonneg _); have hk:0≤ F:= zero_le_one.trans hl
  have hy: 1≤ Real.sqrt X(s):=by nlinarith only [hX,hx,Real.sq_sqrt hx.le,Real.sqrt_nonneg X(s)]
  have hb:0 ≤ T.beta := by linarith only [hx,g.1]
  unfold number temp; let Z:=(Real.sqrt X(s))⁻¹; have hz:0≤Z:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have ha:Z ≤ 1:= (inv_le_one₀ (zero_lt_one.trans_le hy)).mpr hy
  have hd: δ ≤ C₁*((2*Z)*decay β'):=mul_le_mul_of_nonneg_left (epsFund hX v.1).2 p.le
  let D:=decay β'; change C_g*T.beta*(Z*F)*_+_≤ _*D*F
  have hj:= hd.trans (show C₁*(2*Z*D) ≤ C₁*(2*F*D) from by gcongr; exact ha.trans hl)
  have hi: X(s)*Z^2=1:=by rw [← Real.sq_sqrt hx.le, show Z^2= ((Real.sqrt X(s))^2)⁻¹ from inv_pow .., mul_inv_cancel₀]; positivity -- duplicated replacement below
  calc
    _ ≤ |C_g| * (2*X(s))*(Z*F)*(C₁*(2*Z*D)) + |C_p| * (C₁*(2*F*D)):=by gcongr; apply le_abs_self; exact g.2; apply le_abs_self
    _ = (|C_g| * 4*C₁+ |C_p| * 2*C₁)*D*F := by linear_combination 4* |C_g| *C₁*D*F*hi
    _ ≤ _ := by gcongr ?_ * _ * _; change _ ≤ _+1; linarith

variable (P)
/-- on the actual Loom and Gauge with interest prices and widths of this P. LP (44–47). Keep length on all, old and new full. Includes exponential rate and sizes pre-production -- rate uses top and levelQ only. Apply on any high-s checker toggle (any choices already made if patches are disjoint & bought CP1). -/
theorem budget_epoch :
    0 < rate0 ∧ ∃ D:ℝ,0<D ∧ ∀ᶠ s:ℕ in atTop,∀ (i k:ℕ),s≤P.run.uv k → ∀ β':ℝ, matchedX X(s) β'→∀ (m:ℝ)(ξ:SU.group.Color)(neg:Bool),|m|≤24 → ‖ξ‖≤1 →
    let R := Papal.gram P.run s i k; let M:= Papal.count P.run s i; let A:=Papal.room P.run s i;
    let b:=rotorLeft neg m β' ξ; let c:=rotorRight neg m β' ξ;
    ∀ (e:gaugeLink M)(U:Pane M)(y:Ids M),
      let V:=oneOffer e b c U;
      clean (R.p.threshold/3) (rotorWindow P.par.J.n e) V →
      let U0:=A (U,y); let V0:=A (V,y);
      HasSum (Receipt.expense R U V U0 V0) ((↑(R.path.inChannels R.funds R.p R.beta U-R.path.inChannels R.funds R.p R.beta V) : ℂ) + (Pec.pigment R.J.I U0-Pec.pigment R.J.I V0)) ∧
      SumBudget (fun d:Receipt M=> ‖Receipt.expense R U V U0 V0 d‖*Real.exp (rate0 * (Receipt.length R d:ℝ))) (D*(((Real.sqrt β')⁻¹)^(1/8:ℝ))*Real.exp (Real.log (Real.log X(s))^(2:ℕ))) ∧
      (∀ d:Receipt M, Branch.Grove (BPress.Grid.field 4 (W M)) (d.wing R) ∧ (d.wing R).card ≤ d.length R ∧
      (d.expense R U V U0 V0≠0 → e.1∈d.wing R∧ e.1+Lattice.step e.2∈d.wing R)):=by
  have hh:= (Λ).K.top.width_pos; have hl:=level_p (Λ).W.C
  obtain ⟨C1,h1,H⟩:= chartRotor
  refine ⟨lt_min (div_pos hh (by norm_num)) (div_pos hl (by norm_num)),number P C1,?_,?_⟩
  · unfold number; positivity
  filter_upwards [(turnover (Λ)).eventually H,(turnover (Λ)).eventually (eventually_ge_atTop (2:ℝ))] with s hs ht i k hr β' he m ξ neg hv hf R M A b c e U y V v U0 V0
  obtain ⟨G1,G2,G3,G4,G5⟩:= Papal.prices_plot P.run s i k hr
  obtain ⟨ha,hb⟩:=hs β' he.1 m hv ξ hf neg
  have hz:R.p.threshold=temp X(s):= by unfold R; rw [G1,(Y0).meter.boot s|>.1]
  rw [←hz] at hb
  have hg:=toggleUp R.p.threshold_pos.le e b c U ha hb v
  have hj: V0=oneOffer e b c U0 := loom_oneOffer b c (Papal.roofage (Y0) i s) R.p.threshold_pos.le (show R.p.threshold ≤ (Λ).J.k from ?_) U y hb v
  · let T:=(Λ).K.top
    have hp: R.path.Bounds R.funds T.width T.paths (Λ).V.W.bar:=by unfold R; rw [G2,G3]; exact (Λ).V.L.mood _
    have hd: 12≤ R.funds.relaxation*T.width :=by unfold R; rw [G3]; exact T.slow_selector
    have hR:∀ j, BPress.chord (V0 j) (U0 j) ≤ C1*rotorEps β':=fun j=> by rw [hj]; exact (one_cost b c U0 j).trans ha
    have hF:∀ j:gaugeLink M,j≠e → V0 j=U0 j:= fun j v=>by rw [hj,one_off _ _ v]
    obtain ⟨H,E⟩:= Receipt.profit R hg hF hR hp hd (show 1 ≤ R.beta by change matchedX X(s) R.beta at G4; linarith only [G4.1,ht]) hl G5.field.2
    exact ⟨H,budget_loosen E (received R ht G1 G3 G4 he h1),fun d=>Receipt.orientation R d hg hF ⟩
  unfold R; rw [G1]; exact P.run.paidM.pole s
universe u
namespace Rhythm
variable {Q:Type u}(E:Q→ gaugeLink n)
variable (β':ℝ)(m:Q→ℝ)(ξ:Q→SU.group.Color)(neg:Q→Bool)(U:Pane n)(z:Ids n)(A:Scree.Loom n)(T:GramM n)
local notation "L0"=>fun j=>rotorLeft (neg j) (m j) β' (ξ j)
local notation "B0"=>fun j=>rotorRight (neg j) (m j) β' (ξ j)

def prism (q:List Q):Pane n:= offer q E (L0) (B0) U

def assemble (q:List Q)(j:Q):Receipt n→ℂ :=
  let v:=prism E β' m ξ neg U q; let v':=prism E β' m ξ neg U (j::q)
  Receipt.expense T v v' (A (v,z)) (A (v',z))

def lamps : List Q→ List (Receipt n→ℂ)
  | []=> []
  | j::q => assemble E β' m ξ neg U z A T q j :: lamps q

def total (q:List Q): ℂ:= ((lamps E β' m ξ neg U z A T q).map (fun f=> (Complex.exp (∑' a,f a)))).prod
variable (S:Q→ Support (More n))(v:∀ j,testRegion (E j).1 (4*(Λ).J.n+24)⊆ S j) -- use r generic
variable {r:ℕ}(v0:∀ j,testRegion (E j).1 (4*r+24)⊆ S j)(h0:Pairwise (Disjoint on S))
include v0 h0
lemma flourish (j:Q)(q:List Q)(p:j∉q)(x:ℝ) (o: clean x (rotorWindow r (E j)) (oneOffer (E j) ((L0) j) ((B0) j) U)) :
    prism E β' m ξ neg U (j::q)=oneOffer (E j) ((L0) j) ((B0) j) (prism E β' m ξ neg U q) ∧
    clean x (rotorWindow r (E j)) (prism E β' m ξ neg U (j::q)) :=by
  have hx(j): (E j).1∈ S j:=v0 j (by simp [testRegion,halo_spec]); have ht: prism E β' m ξ neg U (j::q)= _ := offerCons S E (L0) (B0) U hx h0 q p
  rw [ht]; refine ⟨rfl,?_⟩
  have he: Agrees (testRegion (E j).1 (4*r+24)) (oneOffer _ _ _ (prism E β' m ξ neg U q)) (oneOffer (E j) ((L0) j) ((B0) j) U):=
    one_agrees _ _ (by intro e hi hz; exact (offer_undriven S q E (L0) (B0) U hx h0 p) _ (v0 j hi) (v0 j hz))
  exact (clean_local he x).mpr o
-- assembly pricing from individual epoch, general roof needed only there
variable {a D:ℝ}(hm:∀ j,|m j|≤24)(hv:∀ j,‖ξ j‖≤1)
variable (L:∀ (e:gaugeLink n) (U:Pane n) (b:Bool) (m:ℝ) (ξ:SU.group.Color) (z:Ids n), |m|≤24 → ‖ξ‖≤1 →
    let V:=oneOffer e (rotorLeft b m β' ξ) (rotorRight b m β' ξ) U; clean (T.p.threshold/3) (rotorWindow r e) V →
    let Y:=A (U,z); let X:=A (V,z);
    HasSum (Receipt.expense T U V Y X) ((↑(T.path.inChannels T.funds T.p T.beta U-T.path.inChannels T.funds T.p T.beta V) : ℂ) + (Pec.pigment T.J.I Y-Pec.pigment T.J.I X)) ∧
    SumBudget (fun d=> ‖Receipt.expense T U V Y X d‖*Real.exp (a* (Receipt.length T d:ℝ))) D)
include L hm hv
lemma groupPrice (q:List Q)(t:q.Nodup)(o:∀ j∈q, clean (T.p.threshold/3) (rotorWindow r (E j)) (oneOffer (E j) ((L0) j) ((B0) j) U)):
    let V:=prism E β' m ξ neg U q;
    (((Complex.exp (-T.v)*Complex.exp (T.betaL A (U,z)))*total E β' m ξ neg U z A T q)) = Complex.exp (-T.v)*Complex.exp (T.betaL A (V,z)) ∧
    ∀ f∈ lamps E β' m ξ neg U z A T q,SumBudget (fun d=> ‖f d‖*Real.exp (a*(Receipt.length T d:ℝ))) D:=by
  induction q with
  | nil=> have he:prism E β' m ξ neg U []=U:= by funext i; change 1*U i*1=U i; simp -- maybe ext too much
          exact ⟨by dsimp only [total,lamps]; rw [he]; simp,by simp [lamps]⟩
  | cons j q ih=>
    intro V; obtain ⟨e,g⟩:=List.nodup_cons.mp t; obtain ⟨hw,h⟩:= ih g (fun k p=>o k (List.mem_cons_of_mem _ p)); let W_:= prism E β' m ξ neg U q
    have ⟨he,hu⟩:=Rhythm.flourish E β' m ξ neg U S v0 h0 j q e _ (o j (List.mem_cons_self))
    rw [he] at hu
    obtain ⟨hh,hC⟩:= L (E j) W_ (neg j) _ _ z (hm j) (hv j) hu
    let F:= assemble E β' m ξ neg U z A T q j; have hg:F= _ := (show F= Receipt.expense T W_ V (A (W_,z)) (A (V,z)) from rfl)
    dsimp only [lamps]
    constructor
    · unfold total; change _ * (Complex.exp (∑' d,F d) * total E β' m ξ neg U z A T q)=_
      rw [mul_left_comm,hw,hg,show V= _ from he]
      let V':=oneOffer (E j) ((L0) j) ((B0) j) W_
      have hb:(∑' d:Receipt n, Receipt.expense T W_ V' (A (W_,z)) (A (V',z)) d)=_:= hh.tsum_eq
      change Complex.exp (∑' d:Receipt n, Receipt.expense T W_ V' (A (W_,z)) (A (V',z)) d) * (Complex.exp (-T.v)*Complex.exp (T.betaL A (W_,z)))=_; rw [hb]
      simp only [GramM.betaL, GramM.H0,←Complex.exp_add,Complex.ofReal_sub]; congr 1; change (↑(T.path.inChannels T.funds T.p T.beta W_) : ℂ)-↑(T.path.inChannels T.funds T.p T.beta V')+(Pec.pigment T.J.I _-Pec.pigment T.J.I (A (V',z)))+(-T.v+(T.v-↑(T.path.inChannels T.funds T.p T.beta W_)-Pec.pigment T.J.I (A (W_,z)))) = -T.v+(T.v-↑(T.path.inChannels T.funds T.p T.beta V')-Pec.pigment T.J.I (A (V',z))); ring -- tune
    intro f hf; rcases List.mem_cons.mp hf with ff|w
    · subst f; change SumBudget (fun d=> ‖F d‖*_) _; rw [hg,show V= _ from he]; exact hC
    apply h _ w
end Rhythm
/-- Concurrent purchases, full compensated scalar and each epoch's LP.7 true-length-charge through LP.6 on all checker copies with shifted input tests collected at U only. -/
theorem scalar_epochs : ∃ C> (0:ℝ), ∀ᶠ s:ℕ in atTop,∀ (i k:ℕ),s≤P.run.uv k → ∀ β':ℝ,matchedX X(s) β'→
    let N:=Papal.count (Y0) s i; let T:=Papal.gram (Y0) s i k; let A:=Papal.room (Y0) s i;
    let τ:= T.p.threshold; let r:=(Λ).J.n;
    ∀ (Q:Type u)(S:Q→Support (W N))(E:Q → gaugeLink N)(m:Q→ℝ)(ξ:Q→SU.group.Color)(neg:Q→Bool),
    (∀ j,testRegion (E j).1 (4*r+24) ⊆ S j) → Pairwise (Disjoint on S) → (∀ j,‖ξ j‖≤1) → (∀ j,|m j|≤24) →
    ∀ q:List Q,q.Nodup → ∀ U:Pane N,∀ z:Ids N,
    (∀ j∈q,clean (τ/3) (rotorWindow r (E j)) (oneOffer (E j) (rotorLeft (neg j) (m j) β' (ξ j)) (rotorRight (neg j) (m j) β' (ξ j)) U)) →
    let W0:=Rhythm.prism E β' m ξ neg U q;
    (((Complex.exp (-T.v)*Complex.exp (T.betaL A (U,z)))*Rhythm.total E β' m ξ neg U z A T q)) = Complex.exp (-T.v)*Complex.exp (T.betaL A (W0,z)) ∧
    ∀ f∈ Rhythm.lamps E β' m ξ neg U z A T q,SumBudget (fun d=> ‖f d‖*Real.exp (rate0 *(Receipt.length T d:ℝ))) (C*(((Real.sqrt β')⁻¹)^(1/8:ℝ))*Real.exp (Real.log (Real.log X(s))^(2:ℕ))):=by
  obtain ⟨_,D,h,H⟩:= budget_epoch P
  refine ⟨D,h,?_⟩
  filter_upwards [H] with s hs i k h β' v N T A τ r Q S E m ξ neg hS hM hξ hm q hq U z g
  apply Rhythm.groupPrice E β' m ξ neg U z A T S hS hM hm hξ _ q hq g
  intro e W0 b m ξ j ht hr V hg Y X
  -- L when i qualifications; shadow h
  have hv:= hs i k ?sells β' v m ξ b ht hr e W0 j hg
  · exact ⟨hv.1,hv.2.1⟩
  assumption
end PureForce.LambdaG
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
