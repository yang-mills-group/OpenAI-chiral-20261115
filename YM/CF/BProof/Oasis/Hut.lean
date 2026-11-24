import YM.CF.BProof.Oasis.Buff
import YM.CF.BProof.Tape.Pear
/-! Use Tickets (on Loft) to pay every micro edge. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory Dew
open Lattice Tenant Lat Cube Tulip Scree Skye Spin Branch Stint Tap Hearth Tape
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
section
variable {D I G:Type}[Fintype I][LinearOrder I]{N:Side}{b:Stage (Site N) I D G}(t:Tag b)
def palette (i:Grain):Tag (mirror b):= match i with
 | none | some false=> signs t.reverseV t
 | some true=> dye t
variable [TopologicalSpace D]{t}
abbrev payC(a p:Pay):=billC a Pay.simple p Pay.simple
abbrev hueD(p q:Pay):= ((payC q .simple).wage ‖unitScale‖).lodge ((payC (Pay.simple.add p) .simple).lodge (payC .simple p))
lemma flashP{A C:Raw D I}{p q:Pay}(u:Earn p t t A)(e:Earn q t t.reverseV C)(g:Grain) : Earn (hueD p q) (dye t) (palette t g) (fun i=>stageP (A i) (C i) g):=by
 cases g with
 | none=> exact ((billing e (Earn.free Pay.simple) (Earn.one t.reverseV) (Earn.free Pay.simple)).scalar le_rfl).change (Pay.lodge_left ..)
 | some i=>
   cases i
   · exact (billing (Earn.free Pay.simple) (Earn.free Pay.simple) u.ccUp (Earn.free Pay.simple)).change (Pay.Wide (Pay.lodge_right _ ((payC (Pay.simple.add p) .simple).lodge (payC .simple p))) (Pay.lodge_right ..))
   exact (billing ((Earn.one t).minus u) (Earn.free Pay.simple) (Earn.free Pay.simple) (Earn.free Pay.simple)).change (Pay.Wide (Pay.lodge_right _ ((payC (Pay.simple.add p) .simple).lodge (payC .simple p))) (Pay.lodge_left ..))
abbrev tint (p q v:Pay):=((hueD p q).mul v).mul (hueD p q)
lemma manacle [Nonempty I]{A C:Raw D I}{T:Raw D (Double.Tree I)}{p q v:Pay}(u:Earn p t t A)(e:Earn q t t.reverseV C)(x:Earn v (dye t).reverseV (dye t) T)(g w:Grain): Earn (tint p q v) (palette t g).reverseV (palette t w) (fun i=> draft (T i) (A i) (C i) g w) :=((transE (flashP u e g)).times x).times (flashP u e w)
structure TariffE (t:Tag b) (p:Pay) (X:D → Leads I) where
 tax : Grain→Grain→ Seal (Site N)→Toll (Double.Tree I)
 arr : Seal (Site N) →D→Leads I
 tick(i j:Grain)(S): Ticket (palette t i).reverseV (palette t j) S (tax i j S) (fun x=> arr S x i j)
 ledger(i j): Ledger p.rate (tax i j) p.cash
 profile(x i j): X x i j=∑ S,arr S x i j
abbrev TariffE.award{p:Pay}{X:D→Leads I}(A:TariffE t p X)(i j:Wind I)(S:Seal (Site N)):= A.tax (seam i).1 (seam j).1 S (bedT i) (bedT j) -- tune seam clash
abbrev TariffE.eye{p:Pay}{X:D→Leads I}(A:TariffE t p X)(x:D)(i j:Wind I)(S:Seal (Site N)):= flank (A.arr S x) i j
lemma TariffE.law{p:Pay}{X:D→Leads I}(A:TariffE t p X)(x:D){i j:Wind I}(h:hotter i j):censor (flank (X x)) i j= ∑ S, A.eye x i j S:=by rw [censor_hot _ h]; unfold flank; rw [A.profile,Matrix.sum_apply]; rfl
lemma TariffE.expo{p:Pay}{X:D→Leads I}(A:TariffE t p X)(i j:Wind I)(S:Support N) : Expo (mirror b) S (bedT i) (bedT j) (A.award i j S) (fun x=>A.eye x i j S):= (A.tick _ _ S).expo _ _
def coins(p:Pay):= Fintype.card Grain*p.cash+1
lemma coin_ge(p:Pay) : 1 ≤ coins p:= by unfold coins; have ht:=p.funding; linarith [show (0:ℝ)≤ Fintype.card Grain*p.cash from (by positivity)] -- tune
lemma StrictAccess {α Y:Type}[Fintype Y][Fintype α][LinearOrder α][DecidableEq Y](b: Y→α→ℝ)(u:∀ i j,0≤ b i j)(r:ℝ)(h:∑ j:α,∑ i:Y,b i j≤r)(k:α): (∑ j:α,∑ i:Y,if hotter k j then b i j else 0)≤r:=by apply le_trans (b:=(∑ j:α,∑ i:Y,b i j)) _ h; apply sum_le_sum; intro j _; apply sum_le_sum; intro i _; split; rfl; exact u ..
variable {V:Type}[Fintype V][DecidableEq V]
theorem TariffE.bright{p:Pay}{X:D→Leads I}(A:TariffE t p X){s:Dew V (Wind I)}{c:Civic N s}(u:∀ x,b.home (seam x).2=c.home x)(e:b.F=terr N): Civic.Bright c A.award p.rate (coins p):=by
 let B:=mirror b
 refine ⟨fun i j S _=>(A.expo i j S).positive,fun i j S _ h=> ?_,?_⟩
 · rw [←e, ←u, ←u]; exact (A.expo i j S).triggered h
 intro i; let m(Y:Support N)(j:Wind I):= A.award i j Y *rent p.rate Y; have he(Y j):0≤m Y j:=mul_nonneg (A.expo ..|>.positive) (rent_pos ..).le; apply StrictAccess m he; unfold coins; rw [add_sub_cancel_right]; let W(j:Wind I):= ∑ Y:Seal (Site N),m Y j
 change (∑ j:Wind I,W j)≤_; rw [← Equiv.sum_comp (chart I).symm,Fintype.sum_prod_type]; apply (sum_le_sum (f:=fun i:Grain=>_) (g:=fun _=>p.cash) (fun a _=>?_)).trans_eq (by simp)
 let b':= (seam i).1; let L:= A.tax b' a; let k:=bedT i; have hp(x:I): W ((chart I).symm (a,x))= saleM p.rate L k (Sum.inl x):=by
    unfold W m award bedT saleM; apply sum_congr rfl; intro s _; rw [show seam _=(a,x) from (chart I).apply_symm_apply (a,x),mul_comm]
 simp_rw [hp]; refine le_trans ?_ ((A.ledger b' a).rows k); rw [Fintype.sum_sum_type]; exact le_add_of_nonneg_right (sum_nonneg (fun j _=> sale_nn (fun T _ _=> (A.tick b' a T).nonn _ _) ..)) -- tune
end
variable {j:ℕ}{a b l r δ c v η:ℝ}{N:Side}{F:Core j a b l r N}
abbrev coreA(x: Loft F δ c v η):Op (Single N):= F.upright (carried x.val.1)
abbrev coreB(x: Loft F δ c v η):Op (Single N):= view x (false,false) 1
def paymentE(x: Loft F δ c v η):Leads (Single N):= draft (driftW x) (coreA x) (coreB x)
lemma chargeV (U:Spin.Ready j a b l r)(d:ℝ)(hv:1≤v)(hc:0<c)(hη:0≤η)(ht:η<1) : ∃ p:Pay,∀{N F}(G:Honor U F d), let t:= (Tape.kiln G.1 c v η).mark; Nonempty (TariffE t p (paymentE (N:=N))):=by
 obtain ⟨x,h⟩:=purchaseV hv U d c; obtain ⟨y,H⟩:= Tape.buys hv hc hη ht U d; refine ⟨tint x x y,?_⟩; intro n F G t; obtain ⟨A,g,p,K,k⟩:= H G; obtain ⟨zi,li,wo,i,w⟩:= h G.1; have he:=Tape.gate G.1 (η:=η) (v:=v) zi; have hz:=est (w η (false,false)) (⟨1,Wick.walk1⟩:Time)
 have hp(i j: Grain): ∃ (M:Seal (Site (More n))→ Raw (Loft F d c v η) (Double.Tree (Single n))) (L:Seal (Site (More n))→Toll (Double.Tree (Single n))), (∀ S, Ticket (palette t i).reverseV (palette t j) S (L S) (M S)) ∧ Ledger (tint x x y).rate L (tint x x y).cash ∧ ∀ Y:Loft F d c v η,paymentE Y i j=∑ S,M S Y:= (manacle he hz K i j).holds
 choose C W h l f using hp; exact ⟨W,fun S x i j=> C i j S x,h,l,fun x i j=>f i j x⟩ -- order tune
end YM.CF.BProof.Oasis
