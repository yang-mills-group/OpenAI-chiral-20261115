import YM.CF.BProof.Tape.Vase
import YM.CF.BProof.Veil.Part
import YM.CF.Cour.Monet
import YM.CF.Spire.Hats
/-! Strong phase parts. Using Screen (order 1 plot costs; INCLUDING for
pigment, from the same silt representation as Tex). Plot costs will be used for
set_option linter.unusedSectionVars false
B-lastQ's variation over the not-near-bad blocks. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BProof.Veil
open Function Filter NormedSpace Finset MeasureTheory RecN
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Tape Stint Oasis Scree Palot Wick Crystal
open Jet Spire Vault Paige Drapes Broc
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {B m:Side}
section Film
variable {s:Side}
lemma rearrange {V:Type}(S T: V→Support s)(w:V→ℝ)(v:∀ i,w i≠0→ T i=S i)(r c:ℝ)(h: Moment.Toll S w r c): Moment.Toll T w r c:=by
 refine ⟨h.nonneg,fun x=>?_⟩; convert! h.pays x using 1; ext i; unfold Moment.hit; by_cases g:w i=0; simp [g]; rw [v i g]

-- tick: inserted anchor; atom: all `Seal S` with ∅→singleton.
abbrev Atom(s:Side):= Support s
def atS(i:Atom s): Support s:= if i=∅ then {0} else i
lemma atmMem(i: Atom s): (atS i).Nonempty:=by unfold atS; split; exact singleton_nonempty _; exact Finset.nonempty_iff_ne_empty.mpr ‹_›
lemma rising(i:Atom s): i⊆ atS i:=by unfold atS; split; simp [*]; rfl
lemma born(i:Atom s)(u:Grove (terr _) i) : atS i=i:=by
 have he{Y:Type}[DecidableEq Y]{i:Seal Y}{T: Branch.Field Y}(g:Grove T i): i.Nonempty:=by induction g with| single x=> exact singleton_nonempty _| join => exact insert_nonempty ..
 exact if_neg (he u).ne_empty
variable {D G:Type}[TopologicalSpace D]
structure LM (s:Side)(Q:Light (Site s) D G)(p:Draw D)(f:D→ℂ)(r c:ℝ) where
 fare : Atom s→ℝ
 value: Atom s→D→ℂ
 plot(i): Flash Q p 1 i (value i) (fare i)
 price: Moment.Toll atS fare r c
 book(x):f x=∑ i,value i x
lemma lightMeter(Q:Light (Site s) D G)(p:Draw D)(v:Q.frame=terr s)(f:D→ℂ){r c:ℝ} (h: Screen Q p 1 f r c): Nonempty (LM s Q p f r c):=by
 obtain ⟨M,C,u,h,y⟩:= h; have he: Moment.Toll id C r c:= by
    apply (tollPrice id (fun i=> (u i).pos) r c).mpr; intro x; apply le_trans _ (h x); unfold Gas.bill_X hitE; simp only [hit0,id]; exact le_of_eq (sum_congr rfl fun i _=>mul_comm ..) -- tune
 refine ⟨C,M,u,rearrange id atS C ?_ r c he,y⟩; intro i e; apply born; rw [←v]; exact (u i).travel e
lemma LM.connect{Q:Light (Site s) D G}{p:Draw D}{f:D→ℂ}{r c:ℝ}(L:LM s Q p f r c)(v:Q.frame=terr s)(i:Atom s)(e:L.fare i≠0): Grove (terr s) (atS i):=by have hp:Grove (terr s) i:=v ▸ (L.plot i).travel e; rwa [born i hp]
end Film
variable {e o p δ W r t a K d:ℝ} {N m B:Side}{j:ℕ}{I:ℝ}
lemma openT (p:ℝ): IsOpen {x: Pane N× Stun N | Lat.Slow x.1 (hook x.2) p }:=by
 unfold Slow; simp_rw [Set.setOf_forall]; apply isOpen_iInter_of_finite; intro i; apply isOpen_iInter_of_finite; intro t; apply isOpen_lt _ continuous_const; apply Continuous.norm; have hz(i:Site (More N)): Continuous (fun x:Pane N× Stun N=>hook x.2 i):=by unfold Dial.hook; fun_prop
 let F : Pane N × Stun N→ E:=fun x=>x.1 (i,t); have hf:Continuous F:= (show Continuous (fun x:Pane N=>x (i,t)) from continuous_apply _).comp continuous_fst; exact (turn_cont.comp (hf.prodMk (hz (i+step t)))).sub (hz i)
lemma stBrace : StandardBorelSpace (Brace.Chord m B e p):=by
 unfold Brace.Chord; let U:=More (mid m B); apply MeasurableSet.standardBorel; exact ((Phase.cover_closed ..).measurableSet.preimage measurable_fst).inter ((openT p).measurableSet) -- tune
abbrev tenement(m B: Side)(δ:ℝ):= CapX m B δ
lemma tenstd: StandardBorelSpace (tenement m B δ):=(Phase.cover_closed ..|>.measurableSet).standardBorel -- add δ declaration
abbrev Lpig(P: Pec.Pride (mid m B))(e K r c:ℝ) := LM _ (Spire.soar m B e) (Spire.aether 1 K e m B) (fun x=>Pec.pigment P x.val) r c
abbrev GG(N:Side):= Pane N × Stun N
def gG(N:Side):= (pine N).together (tent N)
-- package without visible extension here
variable {ho:Odd B.val} -- unused
variable {L:Side}{hp:Odd L.val}{Y:Pricing j L hp (Vault.Thread j)} (g: Grasp Y B e)
abbrev Lhum(m:Side)(M:Tulip.Male)(K r c:ℝ):= LM _ (pWorks m B e g.p) (partQ m B e g.p 1 K) (fun x=> hum m B (g.cost m M) x.val.1 x.val.2) r c
lemma braces {M:Tulip.Male}(D: Lhum g m M K r d)(i:Atom (More (mid m B))): ∃ p:Part (gG (mid m B)) (atS i) (D.fare i),∀ x: Brace.Chord m B e g.p,p.val x.val=D.value i x:=by
 letI:=stBrace (m:=m) (B:=B) (e:=e) (p:=g.p); let u:= D.plot i; refine edited measurable_subtype_coe ?_ u.cont.measurable u.pos u.sumline (fun x y h=>u.reads x y ?_) ?_ -- tune metas Std
 · intro h x; exact ⟨(pWorks m B _ _).dress h x,rfl⟩
 · have he:= (paired i).1 ((gG _).onwards h (rising i)); exact ⟨(pine_eq i).1 he.1,(tent_eq i).1 he.2⟩ -- tune
 intro k x y t; rw [show y=(pWorks m B e g.p).dress k x from Subtype.ext t]; exact u.gauge ..
lemma bPig {D: Pec.Pride (mid m B)}(P:Lpig D e K a t)(i:Atom (More (mid m B))): ∃ p:Part (pine (mid m B)) (atS i) (P.fare i),∀ u:CapX m B e,p.val u.val=P.value i u:=by
 letI:=tenstd (m:=m) (B:=B) (δ:=e); let x:=P.plot i; refine edited measurable_subtype_coe (fun v w=>?_) x.cont.measurable x.pos x.sumline (fun a b h=>x.reads a b ?_) ?_; · exact ⟨(Spire.soar m B e).dress v w,rfl⟩
 · exact (pine_eq i).1 ((pine _).onwards h (rising i))
 intro v a b h; rw [show b=(Spire.soar m B e).dress v a from Subtype.ext h]; exact x.gauge ..
-- buy
lemma hums {Ktest:ℝ}(h:1≤Ktest) : ∃ q:ℝ,0≤q∧ ∀ (m:Side)(M:Tulip.Male), g.roundZ ≤ (mid m B).val → Nonempty (Lhum g m M Ktest (radF g) q):=by obtain ⟨q,h,H⟩:= launder g 1 Ktest h; exact ⟨q,h,fun m M k=>lightMeter _ _ rfl _ (H _ k _)⟩
lemma pens (K:ℝ)(h:1≤K)(p:0≤W)(r:0<t) : ∃ C:ℝ,0≤C∧ ∀ (m B:Side)(U:Pec.Pride (mid m B))(e:ℝ), (∀ x,Pec.cents (node x) (U x) t ≤ W) → Nonempty (Lpig U e K (t/18) C):=by obtain ⟨q,h,H⟩:= Cour.lumpP t r K h 1 W p; exact ⟨q,h,fun m B v e u=>lightMeter _ _ rfl _ (H _ _ _ u e)⟩
end YM.CF.BProof.Veil
