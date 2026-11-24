import YM.SU5.LoomForce.Palette
import YM.SU5.WakeInvestment.CurrentClan
import YM.SU5.Hiro.Lard

/-!
Sector Wick on the precise current and the mixed Staff. Do not count complex
self-normalization cancellations again in other steps. `chargedSlot` for one Mark,
actual election still needs `compass` approximation and Gauge term. This lemma is
about the Wick purchase from actual `noble` formula. Use with the later Broom check.
-/
set_option autoImplicit false
set_option maxHeartbeats 360000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods
     Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Lifted
     Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
     Classical
attribute [local instance] opCStarAlgebra
open YM.CF.Lamour YM.CF.Velvet
open YM.CF.Lamour.Bridge.Celeste
open YM.CF.Py.Rate.LocalLimit.Papal (Weaver household)
open Ballad Hiro

variable {N : Side} {j : ℕ} (R : ℕ) {I : Type*} (V : I→ Cover) (L : I→ Twah.DirSpin)
variable {M : Jill.Male} {x:Wave (Single N)}

def idPrice (N : Side) (u : loomZ I) : Reader0 (Single N) := if u.2.2 then
  en0 R (V u.1) (L u.1) u.2.1 else ex0 R (V u.1) (L u.1) u.2.1
def pairPrice (N : Side) (j : ℕ) (M : Jill.Male) : Chart (loomZ I) :=
  fun i k=> rankG (lake N j M) (idPrice R V L N i) (idPrice R V L N k)
local notation "price_" R:max => pairPrice R V L N j M

lemma roll_one (Q : Route I) (b : Leg I) :
    rollC (ton ∘ idPrice R V L N) (paperS (b::Q)) =
      (sold (N:=N) R (V b.i) (L b.i) b.a b.b)*rollC (ton ∘ idPrice R V L N) (paperS Q) := by
  rw [mul_assoc (ton (en0 (N:=N) R _ _ b.b))]; rfl -- sold head

open Chain (tally) -- hides Emu.tally?
-- avoid ambiguity later

def colorGram (P : loomG I → ℝ) (Q : Route I) := ((paperF Q).map P).prod

def sheetPrice (A : loomG I → ℝ) (B : Leg I) : ℝ := (gPage B).elim 1 A
lemma colorGram_cons (A : loomG I→ℝ) (B : Leg I) (Q : Route I) :
    colorGram A (B::Q)=sheetPrice A B * colorGram A Q := by
  unfold colorGram sheetPrice; rw [paperF_more]; cases p:gPage B <;> simp [Option.elim]

abbrev componentV (X : I → ColorL) : loomG I → ℝ := fun i=> (X i.1) i.2

def routePay (A : loomG I → ℝ)(Z : Chart (loomZ I)) (L : Route I) : ℂ := quoteSpin L Z * ↑(colorGram A L)
def fullPay (A : loomG I → ℝ) (Z : Chart (loomZ I)) (tag : I → Sewer) (L : List I) : ℂ := Chain.tally (booths tag L) (routePay A Z)

abbrev mouthBasis (R : ℕ) (u : Cover) (b : Twah.DirSpin) (X : ColorL) (n : Side) : Sewer → FC (Single n)
  | .some p => (R:ℂ)^3 • SitSpin.raw u p b.1 b.2 n (1,1)
  | .none => Hiro.wrapCurrent u b R n X

def platter (tag : I → Sewer) (X : I → ColorL) (n : Side) (Q : List I) :=
  (Q.map (fun i => mouthBasis R (V i) (L i) (X i) n (tag i))).prod

private abbrev speak1 (N : Side) (X : I → ColorL) (b : Leg I) : FC (Single N) :=
    (b.charge*↑(sheetPrice (componentV X) b)) • (sold R (V b.i) (L b.i) b.a b.b (N:=N))
lemma enum_budget {J A : Type*} [AddCommMonoid A] (B : Finset J) (f : J → A) :
    Chain.tally B.toList f = ∑ i∈ B,f i := Multiset.sum_map_toList B.val f

lemma shutter_tone (U : Cover) (G : Twah.DirSpin) (N : Side) (Z : clan) (s : ColorL):
    (mouthBasis R U G s N (.some Z))=∑ i∈ colors Z, sold (N:=N) R U G i i := by
  change ((R:ℂ)^3 • SitSpin.raw U Z G.1 G.2) N (1,1) = _
  rw [← SitSpin.in_Twah]; exact Twah.bouquet .. -- args might b exact G eta
lemma letter_repr (X : I → ColorL) (Z : Sewer) (i : I) :
    mouthBasis R (V i) (L i) (X i) N Z = Chain.tally (enter i Z) (speak1 R V L N X) := by
  cases Z with
  | some z=>
    rw [shutter_tone,enter,Chain.tally_remap,enum_budget]
    apply Finset.sum_congr rfl; intro j _; change sold (N:=N) R (V i) (L i) j j =
      (1*(↑(sheetPrice (componentV X) { i := i, a:=j, b:=j, field:=none, charge:=1 }):ℂ)) • _
    simp only [sheetPrice, gPage, Option.map_none, Option.elim_none, Complex.ofReal_one, one_mul, one_smul]
  | none=>
    rw [mouthBasis]; let T:=wrapCurrent (V i) (L i) R N
    have h (b : kol) : mug.coord b (X i)=(X i) b:=by simp [mug]
    -- expand
    rw [show wrapCurrent (V i) (L i) R N (X i)=T (∑ j:kol, (mug.coord j (X i)) • mug j) from congrArg T (mug.sum_repr (X i)).symm,
      enter]; simp_rw [map_sum,T] -- tune argument order
    simp_rw [Chain.tally_deck,Chain.tally_remap,enum_budget]
    apply Finset.sum_congr rfl; intro j _; rw [map_smul]; simp_rw [tomato,h, Finset.smul_sum,
      RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl
    intro b _; unfold speak1 sheetPrice; change _=(colorEntry a b (mug j)*↑((X i) j)) • _; rw [mul_comm]; rfl

def solderRoute (X : I → ColorL) (N : Side) (P : Route I) : FC (Single N) :=
  ((shade P)*(colorGram (componentV X) P)) • (rollC (ton ∘ idPrice R V L N) (paperS P))
lemma rep_packet (X : I → ColorL) (tag : I → Sewer) (P : List I) :
    platter R V L tag X N P = Chain.tally (booths tag P) (solderRoute R V L X N) := by
  induction P with
  | nil=>
    change 1=(1*(1:ℂ)) • (1:FC (Single N))+0 -- smul issue should ℂ
    simp
  | cons i P ih =>
    change mouthBasis _ _ _ _ _ _ * platter R V L tag X N P = _
    rw [letter_repr R V L X,ih,←(Chain.tally_shift ..).2,booths,Chain.tally_deck]
    simp_rw [←(Chain.tally_shift ..).1, Chain.tally_remap]; apply Chain.tally_same; intro i u; apply Chain.tally_same
    intro r _; rw [solderRoute,solderRoute,colorGram_cons,shade_more,roll_one R]; unfold speak1
    rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm, smul_smul,Complex.ofReal_mul]
    congr 1; ring

-- expose the normalized actual Sea Wick at **any** arity qualification.
-- reusing the method buying `Hiro.seasons` privately in Lard.lean.
lemma wick_row {Z : Type*} (Q:List Z) (F:Z→Reader0 (Single N)) (hL:∀ i,KeyT (F i) (tickA N))
    (M:Jill.Male)(x:Wave (Single N))(p:Sea (spar j M (1:Pane N)) x)(h:1≤j)(t:Kea.Pad j N):
    alleyR (mateK N) x (rollC (ton ∘ F) Q)=runes (fun i k=> rankG (lake N j M) (F i) (F k)) Q:=by
  have ht:= (pitch M h t.1); let T:= ht.1
  let y:= mateK N; have hv:Sea (Dofu N (Kea.field (too N) j M)) x:= coasting t M ▸ p; have Hy:=tickB N
  have hg: skyGlow y 1 x≠0:= shines T x y hv Hy
  change (inner ℂ y x)⁻¹*inner ℂ y (acts (rollC (ton ∘ F) Q) x)=runes (fun a b=> rankG (lake N j M) _ _) Q
  have v:= Emu.frown T Hy hv F hL Q
  unfold pRead skyGlow at v; simp_rw [quant_one,mul_one,act_one,←ht.2] at v
  rw [skyGlow,quant_one,act_one] at hg; rw [show inner ℂ y _= _ from v,inv_mul_cancel_left₀ hg]

lemma on_row (Q : Route I) (X : I→ ColorL) (p:Sea (spar j M (1:Pane N)) x)(h:1≤j)(t:Kea.Pad j N):
    alleyR (mateK N) x (solderRoute R V L X N Q) = routePay (componentV X) (price_ R) Q := by
  unfold solderRoute; rw [map_smul, wick_row _ _ _ M x p h t]; swap
  · intro i; unfold idPrice; split <;> exact nac_k ..
  unfold routePay quoteSpin pairPrice; rw [smul_eq_mul]; ring

lemma on_docket (Q : List I) (X : I→ ColorL) (p:Sea (spar j M (1:Pane N)) x)(h:1≤j)(t:Kea.Pad j N) (tag : I→ Sewer):
    alleyR (mateK N) x (platter R V L tag X N Q)=fullPay (componentV X) (price_ R) tag Q := by
  rw [rep_packet]; let A:=(alleyR (mateK N) x).toAddMonoidHom
  change A _= _; rw [Chain.tally_addMap]; exact Chain.tally_same (fun i _=> on_row R V L i X p h t)

#print axioms on_docket
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
