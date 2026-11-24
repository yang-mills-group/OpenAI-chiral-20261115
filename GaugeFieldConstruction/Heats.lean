import GaugeFieldConstruction.Raster
import GaugeFieldConstruction.Square

/-!
# R1 Positivity & money inputs
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice
open Vouchers Wick Raster Phys Function Cauchy Row Gap Mirror Conj Finset Window Complex Calibration
open Matter (Slot)
open scoped BigOperators
variable {α β γ : Type*}

abbrev Complete {σ : Type*} (c : Finset σ) (f : σ→σ→Credit) (M : Window σ α) :=
   Valid c M ∧ ∀ i∈c,∀ j∈c,(YM.Maxwell.normal:ℂ)*(f i j).money=M.glance i j

def paint (M : Window GIndex α) := M.Cross (delta Pig)
def skin (M : Window FIndex α) := M.Cross (delta Slot)

variable {c : Finset FIndex} {g : Finset GIndex} {C : Window FIndex α} {R : Window FIndex β} {M : Window GIndex γ}
lemma press_G (Q : Complete g gico M) : Valid (g ×ˢ Finset.univ) (paint M) := together Q.1 (checked_d _)
lemma boxing (Q : Complete g gico M) (i j : Pen) (p : i.1∈g) (r : j.1∈g):
    stare (ge (slide (ket i)) (ket j))=(paint M).glance i j := by
  rcases i with ⟨u,v⟩; rcases j with ⟨s,t⟩
  rw [← heights v u, ← heights t s, shadowG, ge, matchU, paint, Window.crossed,slate]
  change _ = M.glance u s * (if v=t then 1 else 0); split_ifs <;> simp [g_view,Q.2 u p s r]
lemma walk (d) (Q : Complete c (iform d) C) (i j : Mode) (p : i.1∈c) (r : j.1∈c) :
    stare (yarn d (ket i) (ket j))=(skin C).glance i j := by
  rcases i with ⟨u,v⟩; rcases j with ⟨s,t⟩
  rw [← heights v u, ← heights t s,yarn,matchU,skin,Window.crossed,slate]
  change _ = C.glance u s * (if v=t then 1 else 0); split_ifs <;> simp [f_view,Q.2 u p s r]

def PG (M : Window GIndex γ) := (paint M).Cross (paint M)
def PF (C : Window FIndex α) (R : Window FIndex β) := (skin C).Cross (skin R)
def PX (C : Window FIndex α) (R : Window FIndex β) (M : Window GIndex γ) := (PF C R).Cross (paint M)
def fullG (g : Finset GIndex) := (g ×ˢ (Finset.univ (α:=Pig))) ×ˢ (g ×ˢ (Finset.univ (α:=Pig)))
def fullF (g : Finset FIndex) := (g ×ˢ (Finset.univ (α:=Slot))) ×ˢ (g ×ˢ (Finset.univ (α:=Slot)))
def fullX (g : Finset GIndex) (c : Finset FIndex) := fullF c ×ˢ (g ×ˢ (Finset.univ (α:=Pig)))

def BS {ζ : Type*} (U : Flip ζ) (Q : Bil ζ ζ) : Window.Form ζ where
  toFun a := stare ∘ₗ Q (U a)
  map_add' a b := by rw [map_add,map_add,LinearMap.comp_add]
  map_smul' z a := by rw [LinearMap.map_smulₛₗ,map_smul]; apply LinearMap.ext; intro i; exact stare.map_smul _ (Q (U a) i)
lemma glance_g (Q : Complete g gico M) (i j : GaugePair) (p : i∈ fullG g) (r : j∈ fullG g) :
    BS mask (weave' ge ge) (ket i) (ket j)=(PG M).glance i j := by
  obtain ⟨x,y⟩:=Finset.mem_product.mp p; obtain ⟨w,z⟩:=Finset.mem_product.mp r
  change stare (weave' _ _ (mask _) _)=_; rw [← takes i.1 i.2,← takes j.1 j.2,mask,portal,arrive, tick,PG, Window.crossed]
  rw [boxing Q _ _ (Finset.mem_product.mp x).1 (Finset.mem_product.mp w).1, boxing Q _ _ (Finset.mem_product.mp y).1 (Finset.mem_product.mp z).1]
lemma glance_f (A : Complete c (iform true) C) (B : Complete c (iform false) R) (i j : Spair) (p : i∈ fullF c) (q : j∈ fullF c) :
    BS pairM fGap (ket i) (ket j)=(PF C R).glance i j := by
  obtain ⟨u,v⟩:= Finset.mem_product.mp p; obtain ⟨x,y⟩:= Finset.mem_product.mp q
  change stare (fGap (pairM _) _)=_
  rw [shadowF,← takes i.2 i.1,← takes j.1 j.2, f_pay,tick,PF, Window.crossed]
  rw [walk _ A _ _ (Finset.mem_product.mp u).1 (Finset.mem_product.mp x).1, walk _ B _ _ (Finset.mem_product.mp v).1 (Finset.mem_product.mp y).1,mul_comm]
lemma glance_x (A : Complete c (iform true) C) (B : Complete c (iform false) R) (T : Complete g gico M) (i j : Trip) (p : i∈ fullX g c) (u : j∈ fullX g c) :
    BS torso xGap (ket i) (ket j)=(PX C R M).glance i j := by
  obtain ⟨v,t⟩:=Finset.mem_product.mp p; obtain ⟨x,y⟩:= Finset.mem_product.mp u
  change stare (xGap (torso _) _)=_; rw [← takes i.1 i.2,← takes j.1 j.2,torso,portal,x_pay,tick,PX,Window.crossed]
  have ht : stare (fGap (pairM (ket _)) (ket _))=_:= glance_f A B i.1 j.1 v x -- adjust
  rw [ht,boxing T _ _ (Finset.mem_product.mp t).1 (Finset.mem_product.mp y).1]
lemma moneyG (Q : Complete g gico M) : Valid (fullG g) (PG M) := together (press_G Q) (press_G Q)
lemma moneyF (A : Complete c (iform true) C) (B : Complete c (iform false) R): Valid (fullF c) (PF C R) := together (together A.1 (checked_d _)) (together B.1 (checked_d _))
lemma moneyX (A : Complete c (iform true) C) (B : Complete c (iform false) R) (T : Complete g gico M) : Valid (fullX g c) (PX C R M) := together (moneyF A B) (press_G T)

/-- Book system has the proper Bose & grade qualifications, no restriction on spin coefficients within. -/
def Permitted (b : Book) (c : Finset FIndex) (g : Finset GIndex) : Prop := b.2.1∈Area (fullG g) ∧ b.2.1∈bosi ∧ b.2.2.1∈Area (fullF c) ∧ b.2.2.2∈Area (fullX g c)
theorem thermal (A : Complete c (iform true) C) (B : Complete c (iform false) R) (T : Complete g gico M) (b : Book)
    (p : Permitted b c g) : stare (Wick.pair (sky b) b) =
    star b.1 * b.1 + ((PG M).heavy b.2.1 b.2.1 + (PG M).heavy b.2.1 b.2.1) + (PF C R).heavy b.2.2.1 b.2.2.1 + (PX C R M).heavy b.2.2.2 b.2.2.2 := by
  obtain ⟨h,v,t,q⟩ := p
  have hu: stare (gaugeGap (sky b).2.1 b.2.1)= (PG M).heavy b.2.1 b.2.1 + (PG M).heavy b.2.1 b.2.1 := by
    change stare (weave' _ _ (mask _) _ + weave' ge ge (mask _) (Phys.swap _ _))=_
    rw [trace.mp v,map_add]
    have e : stare (weave' ge ge (mask b.2.1) b.2.1)=(PG M).heavy _ _:=(Window.checked (fun i p j=>glance_g T i j p) h h)
    rw [e]
  have hf : stare (fGap (sky b).2.2.1 b.2.2.1)= (PF C R).heavy _ _:= Window.checked (fun i p j=>glance_f A B i j p) t t
  have hg : stare (xGap (sky b).2.2.2 b.2.2.2)= (PX C R M).heavy _ _:= Window.checked (fun i p j=>glance_x A B T i j p) q q
  change stare (Wick.cyc _ _)=_; simp only [Wick.cyc,map_add,map_smul,smul_eq_mul, watch,mul_one,hu,hf,hg]; rfl
lemma one_bit (t : ℂ) : (star t*t).re=Complex.normSq t:= by simpa using pigment 1 t

lemma warmed (A : Complete c (iform true) C) (B : Complete c (iform false) R) (T : Complete g gico M) (b : Book)
    (p : Permitted b c g) (u : b≠0) : 0<(stare (Wick.pair (sky b) b)).re := by
  rw [thermal A B T b p]; simp only [add_re,one_bit]
  have h:= priced (moneyG T) b.2.1; have ht:=priced (moneyF A B) b.2.2.1; have hc:=priced (moneyX A B T) b.2.2.2; have hd:=normSq_nonneg b.1
  by_cases v : b.1=0; swap
  · have he:= normSq_pos.mpr v; linarith
  by_cases y : b.2.1=0; swap
  · have he:= warmth (moneyG T) _ p.1 y; linarith
  by_cases t : b.2.2.1=0; swap
  · have he:= warmth (moneyF A B) _ p.2.2.1 t; linarith
  have hz : b.2.2.2 ≠ 0 := fun z=> u (Prod.ext v (Prod.ext y (Prod.ext t z)))
  have he:= warmth (moneyX A B T) _ p.2.2.2 hz; linarith
end YM.GaugeFieldConstruction.Invoice
