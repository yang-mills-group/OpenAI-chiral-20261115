import YM.CF.BProof.Garden.Crop
import YM.CF.BProof.Veil.Expect
import YM.CF.BProof.Trek.Mesh
import YM.CF.BProof.Trek.Lit
-- ALL first spin pieces outside seam, with real trace split retained in receipts.
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.BProof.Anthem
open Function Filter NormedSpace Finset MeasureTheory
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Tape Hero Stint Oasis Scree Palot Wick Crystal Garden Veil Trek Mark Mapping Angular
open Jet Vault Paige Drapes
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N:Side}{I:Type}[Fintype I](Y:Yard (More N))
structure Manus(N:Side)(I:Type)[Fintype I] where
 floor:I→Support (More N)
 price:I→ℝ
 page(i:I) : Veil.Part (world N) (floor i) (price i)
 vital (i:I): (floor i).Nonempty
namespace Manus
variable {B L m N: Side} {j:ℕ}{p:Odd L.val} {a b l r c v δ η:ℝ}
variable {D:GramM (mid m B)} {P:Spin.Ready j a b l r} {F: Core j a b l r (mid m B)} {H: Honor P F δ} {p':Pay} {K α C Lr Cp t o ε α' C':ℝ}
variable {Y': Pricing j L p (Vault.Thread j)} {V:Grasp Y' B δ} {x:Loft F δ c v η}
variable (J:Hinge V H c v η p' D.J.I K α C Lr Cp) {y:Pay} {q:Cargo D t o} {M:Oasis.Marks H y c v η}(T:Pantry M q ε)
-- Desk roots real, other choices for map
abbrev Poles(N:Side):=Hinge.Codes N ⊕ KeyP N
def plumb : Manus (mid m B) (Poles (mid m B)) :=
 { floor:= Sum.elim Hinge.aged (cityS D)
   price:= Sum.elim J.fee (cityP M q ε)
   page i:=match i with
    | Sum.inl k=> J.packed k
    | Sum.inr k=> (T.loan k).fstL (tent _)
   vital i:= match i with
    | Sum.inl k=> ⟨_,Hinge.aged_here k⟩
    | Sum.inr k=> city_ne q k } -- tune
lemma care (i:Poles (mid m B))(v:(plumb J T).price i≠0)(R:Oasis.Tube D y t ε o α' C'):Grove (terr _) ((plumb J T).floor i):=by rcases i with i|i; exact J.conducive i v; exact city_heat M q R i v -- tune
lemma rent (R: Oasis.Tube D y t ε o α' C') (z:ℝ)(u:z≤ p'.rate/2)(x:z≤ α)(v:z≤ Lr)(w:z≤ α'/4): Moment.Toll (plumb J T).floor (plumb J T).price z (((vaultPay p' quota+(vaultPay p' quota+vaultPay p' quota))+(C+Cp)) +(Cargo.roomAge D.p.B (o+o)+4*C')) := Moment.Toll.sum _ _ (J.income z u x v) _ _ ((city_pay M q R).weaken _ _ w le_rfl)
abbrev val (U:Manus N I)(i:I):= (U.page i).val
theorem tally (x:Loft F δ c v η)(Z:Pane (mid m B))(X:Stun (mid m B)) : (∑ i,(plumb J T).val i (eyeWorld Z (sion x) X))=steam J T Z X x:=Fintype.sum_sum_type .. -- tune
variable {s:Side}(U:Manus N I)(Y:Yard (More N))(i:Y.Index)(r:ℕ)
def Shallow(x:Site (More N)) := ∃ j,Y.Vic j r (time x)
def keen (k:I):= U.floor k⊆ Y.band i ∧ ∀ x∈ U.floor k,¬ Shallow Y r x
def sung := univ.filter (fun k:I=>keen U Y i r k)
def mist := univ.filter (fun k:I=>∀ i:Y.Index, k∉U.sung Y i r)
lemma distinct {i j:Y.Index}{k:I}(p:k∈ U.sung Y i r)(h:k∈ U.sung Y j r) : i=j:=by
 obtain ⟨x,g⟩:=U.vital k; exact (Y.u_part i _ (mem_strip.mp ((mem_filter.mp p).2.1 g))).symm.trans (Y.u_part j _ (mem_strip.mp ((mem_filter.mp h).2.1 g)))
def fee (x:World N):ℂ:= ∑ k∈ U.sung Y i r,U.val k x
def rest (x:World N):ℂ:=∑ k∈U.mist Y r,U.val k x
lemma deliver (x:World N): (∑ k:I,U.val k x)=(∑ i:Y.Index,U.fee Y i r x)+U.rest Y r x:=by
 let p:Finset I:=univ.biUnion (fun i:Y.Index=>U.sung Y i r); have hv:U.mist Y r= pᶜ:=by ext k; simp [mist,p]
 have he:=Finset.sum_compl_add_sum p (U.val · x); rw [← he]; unfold rest; rw [hv,add_comm]; congr 1; unfold p fee; rw [sum_biUnion]; intro i _ j _ h; exact disjoint_left.mpr (fun v p t=> h (U.distinct Y r p t)) -- tune syntax
lemma limit {ρ L:ℝ}(w:Moment.Toll U.floor U.price ρ L)(p:0≤ρ)(x:World N): ‖U.fee Y i r x‖≤ (Y.band i).card*L:=by
 let h:= U.sung Y i r; let S:=Y.band i; let hit:= Moment.hit U.floor U.price ρ; apply (norm_sum_le ..).trans; apply (sum_le_sum (fun i _=> (U.page i).cost x)).trans; apply le_trans (b:=∑ k∈h,∑ x∈S,hit x k)
 · apply sum_le_sum; intro k hk; obtain ⟨x,t⟩:=U.vital k; apply le_trans (b:= hit x k) _ (single_le_sum (fun i _=> (w.pays i).1 k) ((mem_filter.mp hk).2.1 t)); unfold hit Moment.hit; rw [if_pos t]; exact le_mul_of_one_le_left (w.nonneg k) (Real.one_le_exp (by positivity))
 rw [sum_comm]; apply le_trans (sum_le_sum (fun i _=> Push.AbsoluteSums.budget_sum (w.pays i) h)); exact (by simp [S])
@[fun_prop] lemma feeMeas : Measurable (U.fee Y i r):= Finset.measurable_sum _ (fun i _=>(U.page i).meas)
lemma feeAgree{x y:World N}(h:(world N).agree (Y.band i) x y): U.fee Y i r x=U.fee Y i r y:= sum_congr rfl fun i u=> (U.page i).include_b ((world N).onwards h ((mem_filter.mp u).2.1))
lemma feeTwist(g:Geometry N)(x:World N): U.fee Y i r ((world N).act g x)=U.fee Y i r x:=sum_congr rfl fun i hi=>(U.page i).ward _ x
end Manus
section
variable {s:Side}(i:Y.Index)(S:Hall (More N))(f: Ratio s (More N))(U: Pane N)(b:Eyes (More N))
def muses : Tape.Throne N:= (Tape.drawB (summer Y i S f U b) (fun x=>(nightsM ..).1)).val
lemma muse_read (V:Pane N)(p:Agrees (↑(Y.band i)) U V)(z:4≤ (s : Side).val)(e:Width f Y.long)(x:Site (More N))(t:x∈ Y.band i): muses Y i S f U b x=muses Y i S f V b x:= Tape.eq_draw (p:=(nightsM Y i S f U b x).1) (q:=(nightsM Y i S f V b x).1) (Trek.strong Y i S f U b V p z e x t).2
lemma muses_move (g:Geometry N)(u:¬Y.D i) : muses Y i S f (gauge g U) (b*(eye (Y.u i) Y.long g)⁻¹)= Tape.sweepThread g (muses Y i S f U b):=by
 funext i' k; ext1 t; rcases k with ⟨d,l'|l'⟩ -- tune shadow
 · change summer _ _ _ _ _ _ _ _=motion _ (summer _ _ _ _ _ _ _ _); rw [(Trek.wear Y i S f U b g u i').2]; rfl
 change deriv _ _=motion _ (deriv _ _); rw [(Trek.wear Y i S f U b g u i').2]; exact Hero.motionDer _ (nightsM Y i S f U b _).1.2.1 _
def fiddle : World N:= eyeWorld U ((U,∅),muses Y i S f U b) (winter Y i S f U b)
lemma fiddle_move (g:Geometry N)(u:¬Y.D i): fiddle Y i S f (gauge g U) (b*(eye (Y.u i) Y.long g)⁻¹)=(world N).act g (fiddle Y i S f U b):=Prod.ext (Prod.ext rfl (Prod.ext rfl (muses_move Y i S f U b g u))) (funext fun x=>(Trek.wear Y i S f U b g u x).1)
lemma fiddle_read(V:Pane N)(p:Agrees (↑(Y.band i)) U V)(z:4≤ (s : Side).val)(e:Width f Y.long): (world N).agree (Y.band i) (fiddle Y i S f U b) (fiddle Y i S f V b):=by
 have hp:(pine N).agree (Y.band i) U V:= (pine_eq _).mpr p
 exact paired _|>.mpr ⟨(paired _).mpr ⟨hp,(equalize _ _ _).mpr ⟨hp,rfl, (curve_rule _).mpr fun x u=> muse_read Y i S f U b V p z e x u⟩⟩,(tent_eq _).mpr (fun x u=>(Trek.strong Y i S f U b V p z e x u).1)⟩
@[fun_prop] lemma fiddle_m : Measurable (uncurry (fiddle Y i S f)):=by
 let Z:= Street (More N); let h:= measurable_subtype_coe.comp (Tape.skein_m (F:=fun (p:Z)=> summer Y i S f p.1 p.2) (fun p x=> (nightsM Y i S f p.1 p.2 x).1) (fun t x=> (measurable_pi_apply (X:=fun _:Site (More N)=>Stamp) x).comp (storyL Y i S f t))); exact (measurable_fst.prodMk ((measurable_fst.prodMk measurable_const).prodMk h)).prodMk (tideL Y i S f)
end
end YM.CF.BProof.Anthem
