import YM.SU5.FiniteGaugeData.Galope.StrataC
import YM.SU5.FiniteGaugeData.Lapis.Saturn
/-! # Motion price for Eu tubes at BP16 surviving rows. Keep a single candidate F at all sets A and all integrations. -/
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Punch Affiche Lantern Lantern.Cup RouteM Rally
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Syl
open Next.Rank.Axial
variable {n: Side}{G: Gauge}{Z: Finset (Site n)} {M w k:ℕ} {C κ K r β a Δ:ℝ} {P:Bed}{u:Stage}{R:PathData G} {Q H:Finset (Bond n)}
local notation "I" => buy Z k
local notation "J" => Plush G (buy Z k)
local notation "hA" => (denim n)
local notation "TK" => Plush G (denim n)
abbrev units(n:Side):ℝ:= Real.sqrt (tileC n)
lemma unitZ(n: Side) : 0 ≤ units n:= Real.sqrt_nonneg _
lemma unit_sq(n:Side):units n ^2= (tileC n:ℝ):=Real.sq_sqrt (by positivity)
lemma may (h:Z ⊆ zones n M)(v:k≤M): buy Z k ⊆ denim n:=fun i p=> Finset.mem_compl.mpr (excluded h v i p).2.2
private def Eno(n:Side) : ↥(denim n) ≃ (axle n).Free :=Equiv.subtypeEquivRight fun i=> Finset.mem_compl
lemma countF (n:Side) : (denim n).card=unload n:= by rw [← Fintype.card_coe,Fintype.card_congr (Eno n),free_count] -- tune
lemma oftenb (h:Z⊆zones n M)(v:k≤M)(W:Floor P u.clip n a C)(w0:0<a)(hu:0<r)(G:Gauge)(c:ℝ): Motif.drift (inlet (may h v) W w0 hu G) c= Real.sqrt ((disc Z k)* (Fintype.card G.ColorIndex:ℝ)) + ‖1-c‖*Real.sqrt ((parcelM Z k)*(Fintype.card G.ColorIndex:ℝ)):=by
 unfold Motif.drift; rw [show Module.finrank ℝ (Vault (Plush G (denim n)))=(denim n).card*Fintype.card G.ColorIndex from by unfold Vault Plush; rw [finrank_euclideanSpace, Fintype.card_prod,Fintype.card_coe], show Module.finrank ℝ (Vault (Plush G (buy Z k)))=(buy Z k).card* Fintype.card G.ColorIndex from by unfold Vault Plush; rw [finrank_euclideanSpace, Fintype.card_prod,Fintype.card_coe]]; unfold parcelM; rw [Nat.cast_mul,Nat.cast_mul,countF, ← disc_book h v,Nat.cast_add]; congr 2; unfold parcelM; ring
local notation "Target" => Portion n G
-- No e license on cardinal semantics of each Book face yet.Insertion criterion.
structure Opal (L:ℝ)(F:Portion n G→ℝ) :Prop where
 dry: ContDiff ℝ 1 F
 cap: ∃ C:ℝ,∀ x, ‖F x‖ ≤ C
 breeze(x y:Portion n G): |F x-F y| ≤ L*units n*‖x-y‖
 direct(x y:Portion n G)(p:∀ i:Cell n,x (i,false)=y (i,false)): F x= F y
private lemma empty_curl (x:LogField G n)(i j:Cell n) (v:separation i.1 j.1≤w+3)(hx:bid (buy Z k) x)(h: i∉ billsC k w Z): Work.F03.faceCurl j x=0:=by
 have he(y:Bond n)(p:separation j.1 y.1≤1): x (markZ n y)=0:= by
    apply hx; intro t; apply h; obtain ⟨o,q,r⟩:= mem_biUnion.mp t; have hm: separation y.1 i.1≤ w+4:=by rw [separation_comm]; exact (separation_triangle ..).trans ((add_le_add v p).trans le_rfl)
    apply inBooks.mpr; refine ⟨o,q,?_⟩; rw [roomCard,add_assoc]; exact Avenue.extend o _ _ hm (mem_filter.mp (mem_product.mp r).1).1 -- tune $k+(w+4) not defeq?$ yes nat+4.
 ext i; change (d 1 n*ᵥ parts G 1 x i) (j.1,plaquette j.2)=0; rw [d_plaquettes]; let a:=j.2.val.1; let b:=j.2.val.2; have hv(y:Bond n)(p:separation j.1 y.1 ≤ 1): parts G 1 x i (y.1,coord y.2)=0:=by unfold parts; rw [show (y.1,coord y.2)=markZ n y from rfl,he y p]; rfl
 rw [hv (j.1+step a,b) (Work.E03.sep_step j.1 _),hv (j.1,b) (by dsimp; rw [separation_self]; omega),hv (j.1+step b,a) (Work.E03.sep_step j.1 _),hv (j.1,a) (by dsimp; rw [separation_self]; omega)]; ring -- tune matching rw
lemma restrictP {L}{F: Target→ℝ}(hp:Opal L F)(s:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(X:coin J)(w:ℕ)(q:ℝ) : F (q• heatC (billsC k w Z) s A (kickC I X))=F (q•heatC univ s A (kickC I X)):=by
 apply hp.direct; intro i; rw [PiLp.smul_apply,PiLp.smul_apply]; apply congrArg (q • ·); -- avoid private empty_curl.Prove.
 by_cases he:i∈ billsC k w Z; · change (if i∈billsC k w Z then _ else 0)=(if i∈ univ then _ else 0); rw [if_pos he,if_pos (mem_univ _)] -- tune
 have ht:faceCurl i (kickC I X)=0:=by
    exact empty_curl _ i i (by rw [separation_self]; exact Nat.zero_le _) (at_key X) he -- spec w
 change (if i∈ billsC k w Z then xLin u.clip R (kickC I X) (i,false) else 0)=(if i∈univ then xLin u.clip R (kickC I X) (i,false) else 0)
 simp [he, xLin, ht]
-- loom.A
variable {L:ℝ}(F: Portion n G→ℝ)(q:Opal L F)(h:Z⊆zones n M)(v:k≤ M)(W:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(D: Floor P u.clip n a C)(w0:0<a)(hu:0<r)(p:0≤L)
abbrev skyR (x:coin J):= F ((κ*Real.sqrt β)•heatC univ W A (kickC I x))
local notation "τ"=>Real.sqrt β /Real.sqrt r
def High (W:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(D:Floor P u.clip n a C)(F:Portion n G→ℝ) (κ:ℝ)(w0:0<a):ℝ:=∫ x:Vault (Plush G (denim n)), F (κ • castM (denim n) W A D w0 x) ∂stdGaussian _
variable (ep: |κ|≤2)(ht: |Real.sqrt β/Real.sqrt r| ≤ 2)
include p q ep
lemma tariff(x y: Vault TK): |F (κ•castM (denim n) W A D w0 x)-F (κ •castM (denim n) W A D w0 y)| ≤ (2*L*units n)*‖x-y‖:= by
 refine (q.breeze _ _).trans ?_; rw [←smul_sub,←map_sub,norm_smul]; apply (mul_le_mul_of_nonneg_left (mul_le_mul ep (glance (denim n) W A D w0 _) (norm_nonneg _) (by norm_num)) (_root_.mul_nonneg p (unitZ n))).trans_eq; ring
-- Reference expense uses WHOLE candidate $F$, not centered a-priori on surviving pieces.
abbrev Fee(G:Gauge)(n: Side)(L:ℝ)(N Q:ℕ)(κ:ℝ) :ℝ:= 2*L*units n*(Real.sqrt ((N:ℝ)*Fintype.card G.ColorIndex)+‖1-κ‖*Real.sqrt ((Q:ℝ)*Fintype.card G.ColorIndex))
def weather(G:Gauge)(L:ℝ)(Z:Finset (Site n))(k:ℕ)(c:ℝ):= Fee G n L (disc Z k) (parcelM Z k) c+Motion.bill (4*L)*(tileC n:ℝ) -- concentration cost
-- receipt on occupation orientation. Coulomb Stamp assembly later.AX
include ep p q ht h v
lemma windmills: let H:=shine (buy Z k) G D w0; let z:= zodiac P G (buy Z k); let f'(x:coin J) := skyR (Z:=Z) (k:=k) (κ:=κ) (β:=β) F W A x; let Ψ := f' ∘ (bridgeB (r • z) (H.smul hu)); let E:= High W A D F κ w0+ weather G L Z k (Real.sqrt β/Real.sqrt r); Integrable (Real.exp ∘ Ψ) (stdGaussian (Vault J)) ∧ (∫ x,Real.exp (Ψ x)∂stdGaussian (Vault J)) ≤ Real.exp E := by
 intro H z f' Ψ E; let V:= inlet (may h v) D w0 hu G; let c:= (τ); let U:= castM (denim n) W A D w0; let g(x:Vault TK):= F (κ • U x)
 have he(x:Vault J): Ψ x=g (c• V x):=by
    let K:=zodiac P G I; let L':= heatC univ W A (kickC I (bridgeB (r•K) (H.smul hu) x)); unfold g; rw [map_smul,show U (V x)=Real.sqrt r • L' from liftZ _ W A D w0 hu x,smul_smul,smul_smul,_root_.mul_assoc, show c*Real.sqrt r=Real.sqrt β from div_mul_cancel₀ _ (Real.sqrt_ne_zero'.mpr hu)]; rfl
 have heU : ContDiff ℝ 1 g:=  Motif.rankL q.dry κ (glance (denim n) W A D w0)
 let V':ℝ:=2*L*units n; have hV':0≤V':=mul_nonneg (by positivity) (unitZ _)
 obtain ⟨d,hy⟩:=q.cap; have hg(x:Vault TK): ‖g x‖≤d:=hy _
 obtain ⟨hV,y⟩:= Motif.theatre (C:=V') V g (tariff F q W A D w0 p ep) heU hg Ψ c he hV' ht; refine ⟨hV,y.trans_eq (congrArg Real.exp ?_)⟩
 change High W A D F κ w0+ _+_= _; rw [show Motif.drift V c=_ from oftenb h v D w0 hu G c]; unfold E weather
 rw [show Motion.bill (2*V')=Motion.bill (4*L)*(tileC n:ℝ) from ?_]; swap; · unfold Motion.bill V'; rw [show 2*(2*L*units n)=4*L*units n from by ring,mul_pow (4*L),unit_sq]; ring
 exact _root_.add_assoc ..
#print axioms windmills
end Syl
end YM.SU5.FiniteGaugeData.Lapis
