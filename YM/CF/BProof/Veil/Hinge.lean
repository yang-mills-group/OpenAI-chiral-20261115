import YM.CF.BProof.Veil.Busy
import YM.CF.BProof.Veil.Wallet
/-! All of eq:B-primary, on one set of World readings. Strong estimates
kept on original domains (including K-test for derivative-path comparisons).
Borel extensions to raw arguments homing in indicated S. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BProof.Veil
open Function Filter NormedSpace Finset MeasureTheory RecN TraceD Garden
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Tape Stint Oasis Scree Palot Wick Crystal
open Jet Vault Paige Drapes
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {B L m N:Side}{j:ℕ}{ho:Odd L.val}{Y: Pricing j L ho (Vault.Thread j)}{a b l r c v δ η:ℝ} {P:Spin.Ready j a b l r}{F:Core j a b l r N}{H:Honor P F δ} 
abbrev World.x(x:World N):=x.1.2.weather
def leafW {S:Support (More N)}{w:ℝ}(p:Part (gG N) S w): Part (world N) S w:= p.liftC (fun (z:World N)=> (z.x,z.2)) ((measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd) (fun _ _=>rfl) fun _ _ e=> paired S|>.2 ⟨((equalize S _ _).1 ((paired _).1 (show (quiet N).agree S _ _ from ((paired S).1 e).1)).2).1,((paired _).1 e).2⟩ -- tune metavars
namespace Part
variable {S:Support N}{w:ℝ}{D:Type}[MeasurableSpace D]{b:RecN N D}(p:Part b S w)
def func (u:ℂ→ℂ)(t:Measurable u)(h:∀ i, ‖u i‖≤‖i‖): Part b S w:=⟨u ∘ p.val, ⟨p.tag.pos,t.comp p.meas, fun i=>(h _).trans (p.cost _),fun x=> congrArg u (p.include_b x)⟩,fun i x=>congrArg u (p.ward i x)⟩
def negz:= p.func (fun i=> -Spire.zen i) (by unfold Spire.zen; fun_prop) (fun i=> by rw [norm_neg]; exact zen_norm i)
def neg:=p.func (fun i=> -i) measurable_neg (fun i=>(norm_neg _).le)
end Part
section
variable {F: Core j a b l r (mid m B)} {H:Honor P F δ}{I:Pec.Pride (mid m B)}{X:Grasp Y B δ}
variable {p:Pay}{K α C Lr Cp:ℝ} -- K grant, α=P IG, Lr Hum rank.
-- all other prices use global
structure Hinge (G:Grasp Y B δ)(H:Honor P F δ) (c v η:ℝ) (p:Pay)(T: Pec.Pride (mid m B))(K α C Lr Cp:ℝ) where
 T':TraceD H c v η p
 A: Lpig T δ K α C
 J:Lhum G m F.M K Lr Cp
 Bl(i:Desk (mid m B)): Part (window (mid m B)) (zDesk i) (T'.charge i)
 Bl_eq(i x): (Bl i).val (sion x)=T'.items i x
 Sp(i:Atom (More (mid m B))) : Part (pine (mid m B)) (atS i) (A.fare i)
 Sp_eq(i)(x:Spire.CapX m B δ): (Sp i).val x.val=A.value i x
 Gl(i:Atom (More (mid m B))) : Part (gG (mid m B)) (atS i) (J.fare i)
 Gl_eq(i)(x:Brace.Chord m B δ G.p): (Gl i).val x.val=J.value i x
lemma ropes(G:Grasp Y B δ)(v':Occasion c v η)(y:Tickets p P δ c v η F H.1)(z:Lpig I δ K α C)(Z: Lhum G m F.M K Lr Cp): Nonempty (Hinge G H c v η p I K α C Lr Cp):=by
 obtain ⟨T⟩:=trace_d y; choose B b using T.visual v'; choose q u using bPig z; choose R h using braces G Z; exact ⟨T,z,Z,B,b,q,u,R,h⟩
namespace Hinge
variable (pC:Hinge X H c v η p I K α C Lr Cp)
abbrev Codes(N:Side):= TraceD.Desk N ⊕ Atom (More N) ⊕ Atom (More N)
def root(i:Codes N):Site (More N):= Sum.elim (fun i=>(TraceD.proj i).1) (Sum.elim (fun i=>(atmMem i).choose) (fun i=>(atmMem i).choose)) i
def aged(i:Codes N): Support (More N):= Sum.elim zDesk (Sum.elim atS atS) i
lemma aged_here (i:Codes N):root i∈ aged i:=by rcases i with i|(i|i); exact mem_insert_self ..; exact (atmMem i).choose_spec; exact (atmMem i).choose_spec
abbrev fee(i:Codes (mid m B)):= Sum.elim pC.T'.charge (Sum.elim pC.A.fare pC.J.fare) i
theorem income (α' :ℝ)(u:α'≤ p.rate/2)(y:α'≤ α)(v':α'≤ Lr): Moment.Toll aged pC.fee α' ((vaultPay p quota+(vaultPay p quota+vaultPay p quota))+(C+Cp)):=by
 apply Moment.Toll.sum _ _ (pC.T'.motifPrice.weaken _ _ u le_rfl) _ _ ((pC.A.price.weaken _ _ y le_rfl).sum _ _ _ _ (pC.J.price.weaken _ _ v' le_rfl)) -- tune
lemma conducive(i:Codes (mid m B))(v:pC.fee i≠0): Grove (terr _) (aged i):=by
 rcases i with i|(i|i); exact pC.T'.shapes i v; exact pC.A.connect rfl i v; exact pC.J.connect rfl i v
def packed : ∀ i:Codes (mid m B), Part (world (mid m B)) (aged i) (pC.fee i) := fun i=> match i with
 | Sum.inl i => ((pC.Bl i).sndL (pine (mid m B))).fstL (tent _)
 | Sum.inr (.inl i) => (leafW ((pC.Sp i).fstL (tent _))).neg
 | Sum.inr (.inr i) => (leafW (pC.Gl i)).negz
-- real path transport equality conditions support receipts used on originals
lemma foldT(z:Pane (mid m B))(x:Loft F δ c v η)(u:Stun (mid m B))(d:Slow (carried x.val.1) (Dial.hook u) X.p) :
 (∑ i,(pC.packed i).val ((z,sion x),u))= keyF x-Spire.zen (Tape.buh (U:=m) X x u)-Pec.pigment I (Tape.carried x.val.1):=by
 let N:=mid m B; let t:=carried x.val.1; let k:Spire.CapX m B δ:=⟨t,x.val.1.val.1.property⟩; let Z: Brace.Chord m B δ X.p:=⟨(t,u),x.val.1.val.1.property,d⟩
 rw [Fintype.sum_sum_type]; nth_rw 2 [Fintype.sum_sum_type]; change (∑ i,(pC.Bl i).val (sion x))+((∑ i, - (pC.Sp i).val k.val)+(∑ i, -Spire.zen ((pC.Gl i).val Z.val)))=_; simp_rw [pC.Bl_eq,pC.Sp_eq,pC.Gl_eq,sum_neg_distrib]; rw [pC.T'.totalT]; unfold Spire.zen; rw [←mul_sum, ←Complex.ofReal_sum,←Complex.im_sum,←pC.A.book,←pC.J.book]; change keyF x+(-Pec.pigment I t + -(Complex.I * ↑(Tape.buh X x u).im))=_; abel
end Hinge
end
end YM.CF.BProof.Veil
