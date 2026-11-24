import YM.SU5.FiniteGaugeData.CodaT.Pep
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open YM.SU5.FiniteGaugeData.CodaT Eight
/-! # Authorized source for Leaning program. -/
open Fock.Reduction.Drama.Pack Fock.Relief YM.SU5.FiniteGaugeData.Cuprite.Spirit
variable {N M:Side}{S:Finset Cover}{T U:Finset (Site N)}{K:Calibration}{W':W K}{c r s t ε ν H:ℝ}{G Q:Op (Single N)}{n m k d w:ℕ}
-- matching natural currencies for any wired bilinear (WP18). Does not need aligning at planar origins. We construct explicitly so basis signs checked on tiny wrapped endpoints, to read moving slope for this family stencil. Here `Spin10`/`δ5` each paid, upper/lower. Common law on gauge. -/
namespace Niagara
variable {x y a b:Cover}{u v:SpinIdx}
structure Chisel where
 σ: Window.Family
 launch : Cover
 landing: Cover
 line : Walk
 activate: stop (nodeC launch) line=nodeC landing
 u:SpinIdx
 d:SpinIdx
 up:u∈plusHalf
 dn:d∉plusHalf
namespace Chisel
variable (X:Chisel)
-- π index at matter site
abbrev upCard(X:Chisel)(N:Side):Site N × SpinIdx:= (wrap N X.launch,X.u)
abbrev downCard(X:Chisel)(N:Side):Site N × SpinIdx := (wrap N X.landing,X.d)
abbrev town(X:Chisel):Finset Cover:=(visits (nodeC X.launch) X.line).toFinset
local notation "S₀"=> X.town
lemma birth : nodeC X.launch∈ X.town:=by unfold town; cases e:X.line<;> simp [visits]
private lemma finish0 (u:Cover)(l:Walk): stop u l∈ visits u l:=by induction l generalizing u <;> simp_all [stop,visits]
lemma finish: nodeC X.landing∈ X.town:= List.mem_toFinset.mpr (X.activate ▸ finish0 (nodeC X.launch) X.line)
lemma unequal(N:Side): X.downCard N≠ X.upCard N:=fun h=> X.dn (by rw [show X.d=X.u from congrArg Prod.snd h]; exact X.up)
-- wire. conjugate at landing. payroll exact.
def runWire (U:LinksC):SU.E:= travel U (nodeC X.launch) X.line
abbrev runE(U:Pane N):= runWire X (onC N U)
lemma shifts(U:Pane N)(g:Mosquito N): X.runE (Lattice.gauge g U)=g (node (wrap N X.launch))* X.runE U * (g (node (wrap N X.landing)))⁻¹:=by unfold runE runWire onC; rw [expandAt_gauge, travel_gauge, X.activate,node_of,node_of,add_zero,add_zero]
lemma partner {n:Side}(U V:Pane n)(g:Agrees (region X.town n) U V): X.runE U=X.runE V:=travel_local (nodeC X.launch) X.line (onC n U) (onC n V) ((fun e p q=> on_agree n g e (List.mem_toFinset.mpr p) (List.mem_toFinset.mpr q))) -- tune
-- common multiplicity. use cutM twice. theta mirror support in Post
local notation "ρ"=> fun x:SU.E=>(matter x).val
local notation "μ"=> colors X.σ
abbrev internal(W:SU.E):= cutM (colors X.σ)*(matter W).val*cutM (colors X.σ)
abbrev surfN(U:Pane N): Op (Single N):=Tulip.panel (X.upCard N) (X.downCard N) (X.internal (X.runE U))
-- lift actual winding, ensures Eu K Family in this slot
abbrev shiftSign(N:Side):ℂ := winding N X.launch * star (winding N X.landing)
abbrev buyD(N:Side): Sourced N:=fun V=> X.shiftSign N • X.surfN V
abbrev currentOf(K:Calibration): Family K:= fun m=> projectF (X.buyD (K.c m)) -- ambiguous
lemma valInt (V:SU.E)(i j:SU.Slot): X.internal V i j=if i∈ μ ∧ j∈ μ then (matter V).val i j else 0:=by unfold internal cutM; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]; by_cases p:i∈ μ <;> by_cases q:j∈ μ <;> simp [p,q] -- tune
lemma posData (V: Pane N)(g:Mosquito N): X.buyD N (gauge g V)=twist (tradew N g) (X.buyD N V):=by
 unfold buyD surfN; rw [twist_scalar,shifts]; congr 1
 let H := tradew N g; let W:= X.runE V; let x:=X.upCard N; let y:= X.downCard N; let W':= g (node x.1)*W*(g (node y.1))⁻¹
 have he(V:SU.E)(a b:Site N × SpinIdx) : tap (panel x y (X.internal V)) a b= if a=x ∧ b=y then X.internal V else 0:= by ext i j; by_cases p:a=x∧ b=y <;> simp [panel,tap,p]
 have hp (a b: Site N × SpinIdx) : tap (sings false H (panel x y (X.internal W))) a b=tap (panel x y (X.internal W')) a b := by
    change tap (sings false (portX (Equiv.refl (Site N × SpinIdx)) (fun i=> matter (g (node i.1)))) _) _ _= _; rw [tap_sg (p:=Equiv.refl (Site N × SpinIdx)) (F:=fun i=> matter (g (node i.1))),he,he]
    by_cases h:a=x ∧ b=y; swap; · simp only [Equiv.refl_apply,if_neg h,win_z,mul_zero,zero_mul]
    rw [h.1,h.2]; simp only [Equiv.refl_apply, true_and, if_true]; unfold W' internal; rw [map_mul,map_inv,map_mul]
    let Z:=cutM (colors X.σ); let A:=matter (g (node x.1)); let Y:=matter (g (node y.1))
    change A.val*(Z*(matter W).val*Z)*star Y.val=Z*(A.val*(matter W).val*star Y.val)*Z
    have ht:A.val*Z=Z*A.val:= (matter_block ..).eq; have hu:star Y.val*Z=Z*star Y.val:= by
      have he:= (matter_block X.σ (g (node y.1))⁻¹).eq; rw [map_inv] at he; exact he
    simp_rw [mul_assoc] at *; rw [←mul_assoc A.val Z,ht,mul_assoc]; simp only [mul_assoc,←hu]
 ext ⟨x,a⟩ ⟨y,b⟩; exact (congr_fun (congr_fun (hp x y) a) b).symm
lemma kept(U:Pane N) : Cellar (modesIn N (region X.town N)) (X.buyD N U):=by
 let W:=X.internal (X.runE U); let S:=region (S₀) N; let A:=X.upCard N; let B:=X.downCard N; let C:=modesIn N S
 have h(x:Site N×SpinIdx)(i:SU.Slot): (x,i)∈C↔ node x.1 ∈ S:=modes_at ..
 have hv:node A.1∈S:=by unfold A upCard; dsimp only; rw [node_of]; exact mem_image_of_mem _ X.birth
 have hx:node B.1∈S:=by unfold B downCard; dsimp only; rw [node_of]; exact mem_image_of_mem _ X.finish
 have hp: Cellar C (panel A B W):=by
    constructor <;> ext ⟨x,i⟩ ⟨y,j⟩ <;> (first| rw [cutM,Matrix.diagonal_mul]| rw [cutM,Matrix.mul_diagonal]) <;>by_cases t:x=A∧y=B
    all_goals simp [panel,t] <;> simp [h,hv,hx]
 change Cellar C (_ • panel A B _); exact ⟨by rw [Matrix.mul_smul,hp.leftP],by rw [Matrix.smul_mul,hp.rightP]⟩
-- triangle exact.
lemma sig (U:Pane N): let T:= X.buyD N U; T*T=0 ∧ Matrix.trace T=0 :=by
 let A:=X.upCard N; let B:=X.downCard N; let D:= panel A B (X.internal (X.runE U)); have he:B≠A:= X.unequal N
 have hp: D*D=0:=by ext ⟨x,i⟩ ⟨y,j⟩; rw [Matrix.mul_apply]; exact sum_eq_zero fun ⟨b,t⟩ p=> by by_cases h:b=B<;> simp [D,panel,h,he, Ne.symm he]
 have hh:Matrix.trace D=0:=by unfold Matrix.trace; refine sum_eq_zero fun ⟨x,i⟩ p=> ?_; rw [Matrix.diag_apply]; by_cases h:x=B<;> simp [D,panel,h,he] -- tune h notation
 intro T; change (_ • D) * (_ • D)=0 ∧ Matrix.trace (_ • D)=0; rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.trace_smul,hp,hh,smul_zero,smul_zero,smul_zero]; trivial
-- Panel bound via swap.
private lemma panel_b (x y:Site N×SpinIdx)(D:Op SU.Slot): ‖panel x y D‖ ≤ ‖D‖:= by
 let e:=Equiv.swap x y; let f(i:Site N×SpinIdx):=if x=i then D else 0
 have he:panel x y D= jump e f:=by
    ext ⟨a,b⟩ ⟨t,u⟩; by_cases p:x=a; · rw [←p]; rw [jump_apply]; by_cases h:t=y<;> simp [panel,f,e,h,Eq.comm (a:=y)]
    simp [panel,p,jump_apply,f,Ne.symm p]
 rw [he]; exact jump_bound _ _ (norm_nonneg _) (fun i=>by unfold f; split; rfl; rw [norm_zero]; exact norm_nonneg _)
private lemma wrist(W:Op (Single N)): ‖X.shiftSign N • W‖=‖W‖:=by rw [norm_smul,shiftSign,norm_mul,norm_star]; unfold Lifted.winding; rw [fee_norm,fee_norm]; simp
lemma wake(U:Pane N): ‖X.buyD N U‖ ≤1:=by
 rw [buyD,wrist]; refine (panel_b ..).trans ((Reduction.Drama.needy' ?_ _).trans ((Reduction.Drama.needy ?_ _).trans (le_of_eq ?_))) -- tune needy in Pack.mean.
 · exact cutM_idp _
 · exact cutM_idp _
 exact CStarRing.norm_of_mem_unitary (matter _).property
lemma noteE(U:Pane N) : ‖X.buyD N U-X.buyD N 1‖= ‖panel (X.upCard N) (X.downCard N) (X.internal (X.runE U)-X.internal (X.runE (1:Pane N)))‖:=by
 unfold buyD surfN; rw [← smul_sub,X.wrist]; apply congr_arg; ext i j; by_cases p:i.1=X.upCard N ∧ j.1= X.downCard N<;> simp [panel,p] -- tune
private lemma baseC(U:SU.E): Continuous fun W:SU.E=> X.internal W:= by unfold internal; apply Continuous.mul _ continuous_const; apply Continuous.mul continuous_const; exact matter_cont
lemma run_o: X.runE (1:Pane N)=1:=by
 have he: onC N (1:Pane N)=1:=rfl; unfold runE runWire; rw [he]; generalize nodeC X.launch=x; generalize X.line=y; induction y generalizing x with| nil=>rfl| cons i l ih=> rw [travel,ih]; simp [Step.read, Step.used]
private lemma pace(a:Cover)(t:ℝ)(U:LinksC)(V:Walk)(h:∀ e:Edge Cover,e.1∈ visits a V→e.1+step e.2∈ visits a V→ SU.group.chord (U e) ≤t): SU.group.chord (travel U a V)≤ t*V.length:=by
 induction V generalizing a with
 | nil=> change SU.group.chord 1≤t*(↑(0:ℕ):ℝ); rw [Gauge.chord_one]; simp
 | cons i V ih=>
    rw [travel]; have hz: a∈ visits a (i::V):=List.mem_cons_self; have hh(z)(q:z∈ visits (a+i.vec) V): z∈visits a (i::V):=List.mem_cons_of_mem _ q; have ht : a+i.vec∈ visits a (i::V):= hh _ (by cases V <;> simp [visits]); apply (Gauge.chord_triangle ..).trans; refine (add_le_add (b:=t) ?_ (ih _ (fun i p q=> h i (hh _ p) (hh _ q)))).trans_eq (by rw [List.length_cons,Nat.cast_add,Nat.cast_one]; ring); rcases i with ⟨i,u⟩; cases u; exact h (a,i) hz ht; change SU.group.chord (U (a-step i,i))⁻¹ ≤_; rw [Gauge.chord_inv]; refine h _ (by simpa only [sub_eq_add_neg,Lattice.Step.vec,ite_true] using ht) ?_; rw [show ∀ (r s:Cover),(r-s)+s=r from sub_add_cancel]; exact hz
lemma wireB(t:ℝ) (U:Pane N)(h:fieldR (region X.town N) t U): SU.group.chord (X.runE U) ≤ t*X.line.length:=by
 refine pace _ _ _ _ (fun e p q=>?_); rw [onC_spec]; refine h (wrap (More N) e.1,e.2) (mem_image_of_mem _ (List.mem_toFinset.mpr p)) ?_; change wrap (More N) e.1 + step e.2∈ _; rw [← wrap_step, ← map_add]; exact mem_image_of_mem _ (List.mem_toFinset.mpr q)
lemma earth(p:0<ε): ∃ r:ℝ,0<r∧∀ (N:Side)(U:Pane N), fieldR (region X.town N) r U→ ‖X.buyD N U - X.buyD N 1‖≤ ε:=by
 let S:Set SU.E:={y| ‖X.internal y-X.internal 1‖< ε}; have hp:S∈𝓝 (1:SU.E):= ((baseC X 1).sub continuous_const).norm|>.continuousAt|>.tendsto|>.eventually (gt_mem_nhds (by change ‖X.internal 1-X.internal 1‖ <_; rw [sub_self,norm_zero]; exact p))
 obtain ⟨r,h,t⟩:= Next.Rank.surrounds SU.group _ hp; let n:ℝ:=X.line.length+1; have he:0<n:=by unfold n; positivity
 let v:=r/n; have hx:0<v:=div_pos h he; refine ⟨v,hx,fun N U z=>?_⟩; rw [noteE,X.run_o]; apply (panel_b ..).trans (le_of_lt ?_); apply t; exact (wireB X v U z).trans (le_trans (mul_le_mul_of_nonneg_left (by unfold n; linarith only []:(X.line.length:ℝ)≤ n) hx.le) (div_mul_cancel₀ _ he.ne'|>.le)) -- tune t infer
def fullSplice(CP:Calibration)(i j: SU.Slot): Family CP:=Buffered.scalar CP ((fun W:LinksC=> (matter (X.runWire W)).val i j) ∘ Prod.fst) * (creation CP X.launch X.u i * removal CP X.landing X.d j)
def script(CP:Calibration): Family CP:=∑ i∈colors X.σ,∑ j∈colors X.σ, X.fullSplice CP i j
-- explicit term formula, includes every occupancy mode in slot. all in true stencils.
private lemma dg_smul (c:ℂ)(X:Op (Single N)):dg (c• X)=c • dg X:=by unfold dg dyad; simp only [Matrix.smul_apply,smul_sum,smul_eq_mul,smul_smul]
set_option maxHeartbeats 1600000 in
private lemma gDyad (x y : Site N × SpinIdx) (V : SU.E) : dg (panel x y (X.internal V))=∑ i∈colors X.σ, ∑ j∈ colors X.σ,(matter V).val i j • (put (x,i)*takeF (y,j)) := by
 let f(i j:Single N):= (panel x y (X.internal V)) i j • (put i * takeF j)
 change ∑ i,∑ j, f i j=_
 have hp (a : Site N × SpinIdx) (i : SU.Slot) : ∑ t : Single N, f (a,i) t= ∑ j:SU.Slot, f (a,i) (y,j):=by
    rw [show (∑ t : Single N, f (a,i) t)=_ from Fintype.sum_prod_type (fun k : (Site N × SpinIdx) × SU.Slot=> f (a,i) k), sum_eq_single y]
    all_goals simp_all [f,panel]
 rw [show (∑ i,∑ j,f i j)=_ from Fintype.sum_prod_type (fun k : (Site N × SpinIdx) × SU.Slot=> ∑ j, f k j)]; simp_rw [hp]
 rw [sum_eq_single x]; simp [f,panel,valInt, Window.colors, ite_smul, ite_and,sum_filter]; all_goals simp_all [f,panel]
lemma debt (U:Fields (K.c M))(i j:SU.Slot): X.fullSplice K i j M U=((matter (X.runE U.1)).val i j * X.shiftSign (K.c M)) • (put (X.upCard (K.c M),i)*takeF (X.downCard (K.c M),j)):=by
 unfold fullSplice Buffered.scalar creation removal; simp only [Pi.mul_apply,basisC,map_smul,create_put, Fock.remove,star_smul,Matrix.smul_mul, Matrix.mul_smul,one_mul]; change star (Lifted.winding (K.c M) X.landing) • (Lifted.winding (K.c M) X.launch • ((matter (X.runE U.1)).val i j • (put (X.upCard (K.c M),i)*takeF (X.downCard (K.c M),j))))= _; simp only [smul_smul,shiftSign]; congr 1; ring
lemma play(K:Calibration): X.currentOf K= X.script K:=by
 funext m U; unfold currentOf script projectF buyD surfN; rw [dg_smul,X.gDyad]; simp_rw [Finset.sum_apply,smul_sum, X.debt,←smul_smul]; refine sum_congr rfl fun i _=>sum_congr rfl (fun j _=> by simp only [smul_smul]; congr 1; ring) -- tune
lemma eligibleW(i j:SU.Slot): InTest K false X.town false (X.fullSplice K i j):=by
 refine InTest.mul (InTest.seed (Coeff.fromC false _ ?_ ?_)) (InTest.mul (.creator i X.up X.birth) (.remover j X.dn X.finish));
 · exact (matter_cont.comp (Wilson.continuous_travel _ _)).matrix_elem _ _
 intro V W h; have hh: X.runWire V=X.runWire W:=travel_local (nodeC X.launch) X.line V W (fun e p q=> h e (List.mem_toFinset.mpr p) (List.mem_toFinset.mpr q)); rw [hh]
lemma offW(i j: SU.Slot): IsNilpotent (X.fullSplice K i j):=by
 refine ⟨2,?_⟩; funext m U; simp_rw [Pi.pow_apply, X.debt]; let a:Single (K.c m):= (X.upCard (K.c m),i); let b:Single (K.c m):=(X.downCard (K.c m),j); have he:b≠a:=fun e=> (X.unequal (K.c m)) (congrArg Prod.fst e); rw [smul_pow]; let R:=(put a* takeF b); rw [show R^2=0 from ?_,smul_zero]; rfl
 rw [sq]; unfold R; rw [mul_assoc,←mul_assoc (takeF b),show takeF b*put a= -(put a*takeF b) from eq_neg_of_add_eq_zero_left ((mixed ..).trans (if_neg he)),neg_mul,mul_neg,←mul_assoc,←mul_assoc, put_sq,zero_mul,zero_mul,neg_zero]
private lemma summer (CP:Calibration){S:Finset Cover}{A:Type*}(V:Finset A)(f:A→ Family CP)(p:∀ i∈V,InTest CP true S false (f i) ∧ IsNilpotent (f i)): InTest CP true S false (∑ i∈V, f i) ∧ IsNilpotent (∑ i∈V, f i):=by
 have hg(i:A)(h:i∈V):TestFamily CP true (f i):=⟨⟨S,(p i h).1⟩,by simp⟩;
 exact ⟨InTest.sum V f fun i h=> (p i h).1,Commute.isNilpotent_sum (fun i h=>(p i h).2) (fun i j x v=>(hg i x).comm (hg j v))⟩
lemma receipt(K:Calibration): InTest K false X.town false (X.currentOf K):=by rw [play]; exact InTest.sum _ _ (fun i _=>InTest.sum _ _ fun j _=> X.eligibleW i j)
lemma citizen(K:Calibration):X.currentOf K∈well K:=by
 refine ⟨⟨⟨_,(receipt X K).widen⟩,by simp⟩,?_⟩; change Tint.Durable K _; intro m g U; unfold currentOf projectF; rw [show (simultaneous g U).1= Lattice.gauge g U.1 from rfl,posData, dg_cov]
def DesireB(K: Calibration): Desire K X.town where
 paid:=⟨X.currentOf K,X.citizen K⟩
 at_site:= X.receipt K|>.widen
 fits:= ⟨nodeC X.launch,X.birth⟩
 print:= X.buyD
 ticket m:=rfl
 col m:=X.kept
 nil m U:=(X.sig U).1
 basso m U:=(X.sig U).2
 gauge m g U:= X.posData U g
 owed:=1
 hv:=zero_lt_one
 price m:=X.wake
 melt ε p:= X.earth p
 off:=by
    have he: IsNilpotent (X.script K):=(summer K (μ) _ (fun i h=> summer (S:=X.town) K (μ) _ (fun j h' => ⟨(X.eligibleW i j).widen, X.offW i j⟩))).2; rw [←play] at he; obtain ⟨k,h⟩:=he; exact ⟨k, Subtype.ext (by rw [Subalgebra.coe_pow]; exact h)⟩
#print axioms DesireB
end Chisel
end Niagara
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
