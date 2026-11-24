import Organdy.Droplet
import Zephyr.Bed
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra

open _root_.Zephyr.Chern


open Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection

variable {N:Side}
local notation "Ω"=> Single N
lemma cellSum (P:Op Ω)(z:Lattice.Cover):
 Matrix.trace (P * millQ (wrap N z))= ∑ i:IS, P (tag N z i) (tag N z i):=by
 rw [mill_Q,Matrix.trace]
 simp only [Matrix.diag_apply, cutM, Matrix.mul_diagonal, mem_filter,mem_univ,true_and,
    mul_ite,mul_one,mul_zero]
 rw [Fintype.sum_prod_type,Fintype.sum_prod_type,Fintype.sum_prod_type]
 rw [sum_eq_single (wrap N z)]
 · simp [tag]
 · rintro y _ h; simp [h]
 · simp


structure Rising (δ:ℝ)(f:ℝ→ℂ):Prop where
 good: Bud f
 price: δ ≤ (bud f 2).re

variable {A:StemA N} {X Y:SOp N} {b c:ℝ}
lemma Rising.dropSum (h:Rising b (dropArc A X))(k:Rising c (dropArc A Y)):
 Rising (b+c) (dropArc A (X+Y)):=by
 have e:dropArc A (X+Y)=fun v=>dropArc A X v+dropArc A Y v:=by funext; rw [dropArc,Pi.add_apply,Matrix.trace_add]
 rw [e]
 have y:=h.good.bloom.add k.good.bloom
 refine ⟨y.1,?_⟩
 rw [y.bud_eq]
 exact add_le_add h.price k.price

abbrev Need (r:ℕ): Lattice.Cover:=fun _=>r
abbrev Occup (r:ℕ) := Finset.Icc (-(Need r)) (Need r)
lemma slipIn (y:Site N)(r:ℕ)(h:separation 0 y≤r): Lattice.lift y ∈ Occup r:=by
 rw [separation_comm,separation,sub_zero] at h
 refine mem_Icc.mpr ⟨fun i=>?_,fun i=>?_⟩
 · change -(r:ℤ)≤_; have t:=(component_le y i).trans h; omega
 · change _ ≤(r:ℤ); have t:=(component_le y i).trans h; omega


abbrev cellPay (P:SOp N)(u:Op Ω):SOp N:=fun V=>(P V - tickA N) * u
abbrev fullPay(P:SOp N)(m:ℕ):= cellPay P (windmill 0 m)

variable (P:Spine)
/-- The exact function of t on the input of the paid per-site affine jet.
Note that spur winding phases are immaterial: these are diagonal entries. -/
lemma dropCell (z:Lattice.Cover)(M:Male):
 dropArc (stream N) (cellPay (funde P.par.K.j M N) (millQ (wrap N z)))=
  sparSite (N:=N) P.par.K.j M z
  + Function.const ℝ (-Matrix.trace (tickA N * millQ (wrap N z))):=by
 funext t
 rw [dropArc, cellPay, sub_mul,Matrix.trace_sub, cellSum,sub_eq_add_neg]
 rfl

abbrev PresN(P:Spine)(i k s:ℕ):= funde P.par.K.j (blood P.run i k s) (age P.run i s)

lemma payCellsEvery (T:Finset Lattice.Cover):
 ∃ δ:ℝ,0<δ∧∀ᶠ s in atTop, ∀ i k,
   let N:=age P.run i s
   ∀ z∈T,Rising δ (dropArc (stream N) (cellPay (PresN P i k s) (millQ (wrap N z)))):=by
 induction T using Finset.induction_on with
 |empty=> exact ⟨1,one_pos,Eventually.of_forall fun s i k z t=> (notMem_empty z t).elim⟩
 |insert a t _ ih=>
   obtain ⟨δ,hq,l⟩:= (SprigFee.paid P).actual a
   obtain ⟨w,p,b⟩:=ih
   refine ⟨min δ w,lt_min hq p,?_⟩
   filter_upwards [l,b] with s y z i k _ v r
   rcases mem_insert.mp r with g|g
   · subst v; rw [PresN,dropCell]
     exact ⟨(y i k _).1, (min_le_left ..).trans (y i k _).2.le⟩
   · exact ⟨(z i k _ g).good,(min_le_right ..).trans (z i k _ g).price⟩
lemma payFull (m:ℕ):
 ∃ δ:ℝ,0<δ∧∀ᶠ s in atTop, ∀ i k,
   Rising (((2*m)^4:ℕ)*δ)
     (dropArc (stream _) (fullPay (PresN P i k s) m)):=by
 obtain ⟨δ,t,h⟩:=payCellsEvery P (Occup (4*(3*m)))
 refine ⟨δ,t,?_⟩
 filter_upwards [h] with s z i k
 let Q (n:ℕ)(B:Op (Single (age P.run i s))):= Rising (n*δ) (dropArc (stream _) (cellPay (PresN P i k s) B))
 refine boxProp Q m (List.ofFn (id:Axis→Axis)) (0:Site (age P.run i s)) ?_ ?_ millQ ?_
 · have h: dropArc (stream _) (cellPay (PresN P i k s) 0) = fun _=>0:=by funext; simp [cellPay,dropArc]
   have r := Bloom.constant 0
   unfold Q
   rw [h]
   refine ⟨r.1,?_⟩
   rw [r.bud_eq]
   simp
 · intro n n' U V u v
   unfold Q; rw [Nat.cast_add,right_distrib, show cellPay (PresN P i k s) (U+V)=cellPay (PresN P i k s) U+cellPay (PresN P i k s) V by funext;simp [cellPay,mul_add]]
   exact Rising.dropSum u v
 intro y e
 unfold Q
 rw [Nat.cast_one, one_mul]
 exact (wrap_lift y) ▸ z i k _ (slipIn y _ e)

/-- paid uniformly also for all affinely growing probes anchored at
node(origin); asserts strict noncancellation on one explicit probe. -/
structure Flourish (N:Side) (P:SOp N)(m:ℕ)(g:Pane N→ℂ)
 (Y:SOp N)(budget residue δ:ℝ):Prop where
 paid (A:StemA N): Temper 1 A 16 → Lode A (fullPay P m) g Y budget residue
 reel: Rising δ (g ∘ petals (stream N))
 full: Rising (2*δ) (dropArc (stream _) (fullPay P m))

lemma maskedRise {P Y:SOp N}{g:Pane N→ℂ}{m:ℕ}{δ:ℝ}
 (h:∀ A, Temper 1 A 16 → Lode A (fullPay P m) g Y b c)
 (q:Rising (2*δ) (dropArc (stream N) (fullPay P m))) (e:c≤δ):
 Flourish N P m g Y b c δ:=by
 have p:= h _ (stream_mild N)
 refine ⟨h,⟨p.paid,?_⟩,q⟩
 have y:= q.price
 rw [p.sheer.bud_eq,Pi.add_apply,Complex.add_re] at y
 have t:= (Complex.re_le_norm _).trans ((p.leftover 2).trans e)
 linarith

/-- Uniform in levels, periods and choice of *the same* truncations as in the
Ward-current opening. Needs only the CrownCar split and the two genuine
exponential polymer costs. -/
structure Rosy (P:Spine) (a b d:ℝ)(m:ℕ)(D δ:ℝ)(w:ℕ):Prop where
 budget : 0<D
 rank   : 0<δ
 intact : ∀ᶠ s in atTop,∀ i k,
    let N:= age P.run i s
    ∀ (K:Scree.Loom N) (p:BudgetPoint) X Y, w≤p.B/10→ WindowDress K p d →
    Trunk (node (0:Site N)) X (p.B/10) a b d→
    Soak (node (0:Site N)) Y a (Real.exp (-a*((p.B/10:ℕ):ℝ))*b) d →
    (∀ z:Openc (More N) d,fullPay (PresN P i k s) m z.val=X z.val+Y z.val)→
    Flourish N (PresN P i k s) m (chime K p (node 0) X) Y D
        (D*Real.exp (-a*((p.B/10:ℕ):ℝ))) δ

theorem rosyPaid {a b d:ℝ}{m:ℕ}(u:0<a)(z:0<b)(v:0<d)(t:0 < m):
 ∃ D δ w, Rosy P a b d m D δ w:=by
 obtain ⟨W,⟨U⟩⟩:= oily u v 16
 obtain ⟨g,r,e⟩:=payFull P m
 let δ:= ((2*m)^4:ℕ)*g/2
 let D:=W*b
 have Y:0<D:=mul_pos U.bound z
 have G:0<δ:=by unfold δ; positivity
 obtain ⟨w,hw⟩:=exists_nat_gt (D/δ/a)
 refine ⟨D,δ,w,Y,G,?_⟩
 filter_upwards [e] with s h i k N K p X Y' q f j l g'
 set n:=((p.B/10:ℕ):ℝ)
 refine maskedRise ?_ (by rw [show 2*δ=((2*m)^4:ℕ)*g by unfold δ;ring]; exact h i k) ?_
 · intro A H
   have n0: node (0:Site N)=1:=by simpa using node_wrap N 0
   have t':= toned j l g' f U (o:=node (0:Site N)) ((by rwa [n0]): Temper (node 0) A 16)
   rw [show W* (Real.exp (-a*n)*b) = D*Real.exp (-a*n) from by unfold D; ring] at t'; exact t'

 have a0:D/δ/a < n:=hw.trans_le (Nat.cast_le.mpr q)
 have f1:= (div_lt_iff₀ G).mp ((div_lt_iff₀ u).mp a0)
 rw [neg_mul, Real.exp_neg,←div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
 exact f1.le.trans (by
     rw [mul_comm _ δ,mul_comm n a]; exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)) G.le)
