import YM.CF.Bloom.Flux
/-! Supporting algebra verification, ordered projection through one forest
in the concrete FiniteGaugeData normalized-mark analysis. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scree.Volume
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

variable {m n: Type*} [LinearOrder m] [Fintype m] [LinearOrder n] [Fintype n]

private lemma put_through (T U : Op n) (h : U*T=1) (v : Ket n) (y : Wave n) :
    acts (create v) (acts (quant T) y)=acts (quant T) (acts (create (acts U v)) y) := by
  rw [← act_mul, ← act_mul, quant_create, ← act_mul, mul_eq_one_comm.mp h, act_one]

private lemma rem_through (T : Op n) (v : Ket n) (y : Wave n) :
    acts (remove v) (acts (quant T) y)=acts (quant T) (acts (remove (acts (star T) v)) y) := by
  have h:= congrArg star (quant_create (star T) v)
  rw [quant_star,star_mul,star_mul,star_star] at h
  rw [← act_mul, ← act_mul,show remove v*quant T=quant T*remove (acts (star T) v) from h]

private lemma pail_put (i : m ↪ n) (s : Finset n) (h : Deck i s) (v : Ket m) (y : Wave n):
    acts (create v) (pailL i s y)=pailL i s (acts (create (coat i v)) y) := by
  apply PiLp.ext; intro k
  rw [←basis_inner,←basis_inner, pails _ _ h, ←act_inner, ←act_inner]
  rw [show star (create v)= remove v from rfl, show star (create (coat i v))=remove (coat i v) from rfl]
  rw [←hoist_r _ _ h, pails _ _ h]

private lemma pail_rem (i : m ↪ n) (s : Finset n) (h : Deck i s) (v : Ket m) (y : Wave n):
    acts (remove v) (pailL i s y)=pailL i s (acts (remove (coat i v)) y) := by
  apply PiLp.ext; intro k
  rw [←basis_inner,←basis_inner, pails _ _ h, ←act_inner, ←act_inner,remove,remove,star_star,star_star]
  rw [←hoist_c _ _ h, pails _ _ h]

private lemma half_ticket (K P : Op n) (h : Commute P K) (S : star P=P) (v : Ket n)
    (p : acts P v=v) : acts (star (K⁻¹*(1-P)+star K*P)) v=acts K v := by
  have hh : P*star K⁻¹=star K⁻¹*P:= by
    by_cases e:IsUnit K
    · have g:P*K⁻¹=K⁻¹*P:= e.mul_left_cancel (by rw [←mul_assoc, ←mul_assoc,←h.eq,mul_assoc,(Fock.live e).1,mul_one,one_mul])
      calc
        _=star P*star K⁻¹:=by rw [S]
        _=star K⁻¹*star P:=by rw [←star_mul,←star_mul,g]
        _=_ := by rw [S]
    · rw [Matrix.nonsing_inv_apply_not_isUnit K ((Matrix.isUnit_iff_isUnit_det K).not.mp e)]
      simp
  rw [star_add,star_mul,star_mul,star_sub,star_one,S, star_star,sub_mul, hh,h.eq,one_mul,
    act_add,act_sub,act_mul,p,sub_self,act_mul,p,zero_add]

private lemma rel_onto (i : m≃n) (v : Ket n):
    coat i.toEmbedding (trailK i.toEmbedding v)=v := by
  rw [stance]
  apply PiLp.ext; intro j; rw [cut_apply,if_pos ?_]
  unfold lows; exact mem_map.mpr ⟨i.symm j,mem_univ _,i.apply_symm_apply _⟩

variable {M H C L B : Side} {j : ℕ} {ho : Odd L.val} {Y:Pricing j L ho (Thread j)}{e : ℝ} {P : Grasp Y B e}
variable (G:Ratio (mid M B) (mid H B))
local notation "Nc" => mid M B
local notation "Nf" => mid H B

open Phase Brace
private lemma bridge_b (x: nomA M H B) (p : G.count=L) (h : P.roundZ≤(mid M B).val)
    (u : JointB G x e) (z : 0<e) (B' : Male) :
    star (ticketT (Thread j) false B' G (unionP x))*ticketT (Thread j) true B' G (unionP x)=1 := by
  -- witness chart as in construction of Spire.shuttle
  obtain ⟨t,hx⟩:=cue_from x.2
  let Z:=starfish M B x.2 t
  let w:=accordL G x Z
  have hv:=pose_g P z G p h x u Z (starK P.capY z.le u.cg hx)
  exact ((Y.cap G p (P.needed.trans h) B' w hv.glyph).chart true).bridge

def placeOp {j:ℕ} (Q:Op Slot)(B' : Male) (x:nomA M H B) (y:Scree.Phys Nf): Scree.Phys Nc :=
  scaleZ Q (fire (Thread j) G B' (unionP x) (cartsL (switchG G).symm y))

lemma letter_p (x:nomA M H B) (B':Male) (p:G.count=L) (h:P.roundZ≤(Nc).val) (u : JointB G x e)
    (z : 0<e) (X : Haro.SpaceM) (v:Ket (Single Nc)) (w:acts (tickA Nc) v=v) (y:Phys Nf):
    let T:=Scree.Volume.placeOp (j:=j) G X.val B' x
    let C:=Peaks.cloth j B' G (unionP x)
    let R:=plankP Nc X.val
    let V:=trailK (switchG G).symm.toEmbedding (acts C (coat (patchQ G) (acts (exp R) v)))
    acts (create v) (T y)=T (acts (create V) y) := by
  intro T C R V
  let W:=ticketT (Thread j) true B' G (unionP x)
  let U:=ticketT (Thread j) false B' G (unionP x)
  let a:=coat (patchQ G) (acts (exp R) v)
  letI : NormedAlgebra ℚ (Op (Single Nc)):= NormedAlgebra.restrictScalars ℚ ℂ (Op (Single Nc))
  have g:exp R*exp (-R)=1:=by rw [← exp_add_of_commute (Commute.refl R).neg_right,add_neg_cancel,exp_zero]
  have k:Commute (lobe G true) C:=(canUse j L ho).orients _ _ _
  have ha:acts (lobe G true) a=a := by
    unfold a; rw [whale_plus, origin _ _ (reefS_deck ..), ←act_mul,
      show tickA Nc*exp R=exp R*tickA Nc from (Commute.exp_right (plank_tick X.val)).eq, act_mul,w]
  have he: acts (star U) a=acts C a := by
    unfold U ticketT; rw [revI]; dsimp only [Thread]
    rw [lobe_plus,sub_sub_cancel]; exact half_ticket _ _ k (lobe_sq ..).isSelfAdjoint _ ha
  have hl: coat (switchG G).symm.toEmbedding V=acts C a:=rel_onto ..
  unfold T placeOp scaleZ
  rw [map_smul,put_through _ (exp R) g, fire, map_smul,pail_put _ _ (reefS_deck ..),effectK,
    put_through _ (star U) (bridge_b G x p h u z B'),show acts (star U) a=_ from he]
  unfold fire effectK
  rw [cartsL,cartsL, hoist_c _ _ (shelfG _), hl]

-- `p` also makes `ho` available from the chosen block.
lemma letter_r (x:nomA M H B) (B':Male) (_p:G.count=L) (Lodd:Odd L.val) (X : Haro.SpaceM)
    (v:Ket (Single Nc)) (w:acts (tickA Nc) v=0) (y:Phys Nf):
    let T:=placeOp (j:=j) G X.val B' x
    let C:=Peaks.cloth j B' G (unionP x)
    let R:=plankP Nc X.val
    let V:=trailK (switchG G).symm.toEmbedding (acts C (coat (patchQ G) (acts (exp (-R)) v)))
    acts (remove v) (T y)=T (acts (remove V) y) := by
  intro T C R V
  let W:=ticketT (Thread j) true B' G (unionP x)
  let a:=coat (patchQ G) (acts (exp (-R)) v)
  letI : NormedAlgebra ℚ (Op (Single Nc)):= NormedAlgebra.restrictScalars ℚ ℂ (Op (Single Nc))
  have hj:Commute (lobe G true) C:=(canUse j L Lodd).orients _ _ _
  have k:Commute (lobe G false) C:= by rw [lobe_plus]; exact (Commute.one_left _).sub_left hj
  have ha:acts (lobe G true) a=0 := by
    unfold a; rw [whale_plus, origin _ _ (reefS_deck ..), ←act_mul,
      show tickA Nc*exp (-R)=exp (-R)*tickA Nc from (Commute.exp_right (plank_tick X.val).neg_right).eq, act_mul,w,map_zero,map_zero]
  have he: acts (star W) a=acts C a := by
    have hv:lobe G true=1-lobe G false:=circ G false
    have hp:acts (lobe G false) a=a:=by rw [lobe_plus,act_sub,act_one,ha,sub_zero]
    unfold W ticketT; rw [revI]; dsimp only [Thread]
    rw [hv,sub_sub_cancel]; exact half_ticket _ _ k (lobe_sq ..).isSelfAdjoint _ hp
  have hz:star (exp (-R))=exp (-R):=by rw [star_exp,star_neg,show star R=R from plank_h X.property.adj]
  have hl: coat (switchG G).symm.toEmbedding V=acts C a:=rel_onto ..
  unfold T placeOp scaleZ
  rw [map_smul,rem_through,hz, fire, map_smul,pail_rem _ _ (reefS_deck ..),effectK,
    rem_through,show acts (star W) a=_ from he]
  unfold fire effectK
  rw [cartsL,cartsL, hoist_r _ _ (shelfG _), hl]

def Letter (N : Side):Type := Sum
    {v:Ket (Single N) // acts (tickA N) v=v} {v:Ket (Single N) // acts (tickA N) v=0}
def op {N : Side} : Letter N → FC (Single N) := Sum.elim (fun v=>create v.val) (fun v=>remove v.val)

def adv1 (j:ℕ) (Q:Op Slot) (B':Male) (x:nomA M H B): Letter Nc→FC (Single Nf) :=
    let D:=Peaks.cloth j B' G (unionP x)
    let pl:=plankP Nc Q
    let E:=fun v:Ket (Single Nc)=>trailK (switchG G).symm.toEmbedding (acts D (coat (patchQ G) v))
    Sum.elim (fun v=>create (E (acts (exp pl) v.val))) (fun v=>remove (E (acts (exp (-pl)) v.val)))

private lemma letters (x:nomA M H B) (B':Male) (p:G.count=L) (h:P.roundZ≤(Nc).val) (u : JointB G x e)
    (z : 0<e) (X : Haro.SpaceM) (l:List (Letter Nc))(y: Phys Nf):
    let T:=placeOp (j:=j) G X.val B' x
    acts (rollC op l) (T y)=T (acts (rollC (adv1 G j X.val B' x) l) y) := by
  intro T; induction l with
  | nil => simp [rollC]
  | cons i l ih =>
    change acts (op i * rollC op l) (T y)=T (acts (adv1 G j X.val B' x i* rollC _ l) y)
    rw [act_mul, act_mul, ih]; rcases i with a|b
    · exact letter_p G x B' p h u z X _ a.property _
    exact letter_r (j:=j) G x B' p ho X _ b.property _

variable {A:Scree.Loom (mid M B)} {R':Scree.GramM (mid H B)}{A':Scree.Loom (mid H B)} {d:ℝ}{q:Chi}
set_option maxHeartbeats 800000 in
theorem marked_project (E:Girt.BaseL P G R' A A' q d) (T:RG.StepData (More Nc) (More Nf))
    (Q:Haro.SpaceM)(F:Forest (ratio G))(V:Orbit Nc)(W:Orbit Nf)(l:List (Letter Nc)) :
    let K:=carrier P A R' A' G T q d Q.val F V W
    let x:nomA M H B:=(seine G F q d (A' W) (A V),A V)
    let l':= adv1 G j Q.val R'.J.M x
    beamL Nc (acts (rollC op l) K) =
         T.density R'.beta W.1 V.1 • beamL Nf (acts (rollC l' l) (denZ R' P A' W)) := by
  intro K x l'; let t:=placeOp (j:=j) G Q.val R'.J.M x
  let y:= denZ R' P A' W; let y':=acts (rollC l' l) y
  have hp:JointB G x e:= E.trial F (A' W) V
  rw [show K=T.density R'.beta W.1 V.1 • t y from rfl, show acts (rollC op l) (T.density R'.beta W.1 V.1 • t y)=T.density R'.beta W.1 V.1 • (acts (rollC op l) (t y)) from
      map_smul ((acts (rollC op l)).restrictScalars ℝ) _ (t y),map_smul,
    show acts (rollC op l) (t y)= t y' from letters G _ _ E.power E.size hp E.pe Q l y]
  apply congrArg (fun z :ℂ=> T.density _ W.1 V.1 • z)
  unfold t placeOp
  rw [shoulderL]
  change inner ℂ (mateK Nc) _=beamZ _ y'
  rw [show inner ℂ _ _=_ from (Spire.shuttle G E.power E.size x hp E.pe R'.J.M).2 (cartsL (switchG G).symm y')]
  exact Fock.sigh (switchG G).symm.toEmbedding _ (shelfG ..) _ _
end YM.CF.Scree.Volume
#print axioms YM.CF.Scree.Volume.marked_project
