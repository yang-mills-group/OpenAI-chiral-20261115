import YM.SU5.FiniteGaugeData.Poin.Gust
import YM.SU5.FiniteGaugeData.Seld.NewMoon
/-! # Lift, on the word domain of the actual estimate -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Flute MeasureTheory Boundary Probe
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "tt"=>timeAxis
variable {H:Hilbert}{α:Type}(M':Canopy H α)(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ z:E4,M S z Ω.val=Ω.val)
variable {n:ℕ} (p q:Mink.Poincare)
namespace Canopy
variable (t u:M'.Token)(chip:M'.Chip)(g:Test4)(w:List M'.Token)
local notation "D"=>Bench S
local notation "£" x:max=>M'.dep x
abbrev horizon (t:M'.Token): (D →ₗ[ℂ] D):= ℑ S (M'.dep t.1) t.2 (M'.grade t.1)
-- scripts.Proof
local notation "V"=> M'.horizon S
def desire(w:List M'.Token) := (w.map (V)).prod
def bud (w:List M'.Token):= M'.desire S w Ω
abbrev Ticket (w:List M'.Token) := (M'.bud S Ω w).val
abbrev EVal (w:List M'.Token) := inner ℂ Ω.val (M'.Ticket S Ω w)
local notation "L"=>M'.Ticket S Ω
local notation "Q"=> M'.EVal S Ω
def travel (p:Mink.Poincare)(t:M'.Token): M'.Token:= (M'.βL p.Λ t.1, shiftK p t.2)
def reve (t:M'.Token): M'.Token:= (M'.mirrorK t.1,Probe.bar t.2)
abbrev moved (p:Mink.Poincare)(w:List M'.Token):= w.map (M'.travel p)
local notation "Nt"=> M'.moved
lemma chip_star : V (M'.reve t)= ℑ S (star (M'.dep t.1)) (bar t.2) (M'.grade t.1):=by unfold horizon reve; rw [show (M'.dep (mirrorK ..))= _ from spar M' t.1]; rfl
lemma travel_reveal : travel M' p (M'.reve t)= M'.reve (travel M' p t):=by apply Prod.ext; exact (Lowns ..).symm; change (Joint.push p (bar t.2))=bar _; ext1 x; simp [travel,shiftK]
lemma planeV(Tok:M'.Token)(f:List M'.Token) : bud M' S Ω (Tok:: f)= V Tok (bud M' S Ω f):=rfl -- Q notation conflict. 
lemma legPaid(x y:D): inner ℂ (V t x).val y.val=inner ℂ x.val (V (M'.reve t) y).val := by rw [chip_star]; exact sees_κ ..
-- Write as Film(order)
lemma ordinary (t:Fin n→ M'.Token): Rail (fun i=>M'.horizon S (t i)) (Omit S)=M'.desire S (List.ofFn t):=by
 induction n with
 | zero=> rw [List.ofFn_zero]; rfl
 | succ n ih=>
    let A:= Omit (n:=n+1) S; let G(i):= horizon M' S (t i); rw [Rail_step G A]; have he:G=(fun i=> _ ) := (rfl:G=G); rw [show s1 n A=1 from (by cases n with | zero=>rfl | succ n=> rw [s1S]),mul_one]; rw [List.ofFn_succ]; exact congrArg (fun B0=> G 0 * B0) (ih (Fin.tail t))
lemma worlddoc (t:Fin n→M'.Token): Wval M' S Ω (fun i=> (t i).1) (fun i=> (t i).2)= EVal M' S Ω (List.ofFn t):= by change inner ℂ _ (Rail (fun i=>horizon M' S (t i)) (Omit S) Ω).val=_; rw [ordinary]; rfl
@[simp] lemma joins : Nt p (Nt q w)=Nt (p*q) w:=by
 unfold moved; rw [List.map_map]; congr 1; funext i; apply Prod.ext; exact Lmult M' _ _ _; change Joint.push p (Joint.push q i.2)=_; exact congrFun (tailor (n:=1) (fun _=>i.2) p q) 0
@[simp] lemma stayed : Nt 1 w=w:=by
 unfold moved; rw [show travel M' 1=id from funext fun i=> Prod.ext (Lini M' i.1) (by ext1 x; simp [travel,shiftK])]; exact List.map_id _
variable (K: Mink.Lorentz)
include hΩ
lemma amber (h:M'.Warrant S Ω)(e: ∀ b:Mink.Ray,Shelf S (magnet b)): Q (Nt (Poincare.motion K) w)= Q w:= by
 suffices he:∀ n (t: Fin n→ M'.Token), Q (Nt (Poincare.motion K) (List.ofFn t))=Q (List.ofFn t) from List.ofFn_get w ▸ he w.length w.get
 intro n t; unfold moved; rw [List.map_ofFn,←worlddoc, ←worlddoc]; exact (drumm M' S Ω hΩ (fun i=>(t i).1) K (fun i=> (t i).2) h e).symm
lemma bring (g:E4): usher S g (M'.bud S Ω w)=M'.bud S Ω (Nt (Poincare.translation g) w):=by
 let p:=Poincare.translation g; induction w with
 | nil=> exact Subtype.ext (hΩ g)
 | cons t w ih=>
    unfold moved at ih ⊢; rw [List.map_cons,planeV,planeV, horizon,attends, ih,horizon,travel]; congr 2; simp [Poincare.translation]
lemma voyage (p:Mink.Poincare)(h:M'.Warrant S Ω)(e:∀ b:Mink.Ray,Shelf S (magnet b)): Q (Nt p w)=Q w:=by
 let p':= Poincare.translation p.b; let K:=Poincare.motion p.Λ; rw [show p=p'*K from by apply Poincare.ext <;> simp [p',K,Poincare.translation,Poincare.motion], ← joins]; unfold EVal Ticket; rw [← bring _ _ _ hΩ] -- rw `p` in p' K.Simp let.V
 nth_rw 1 [← hΩ p.b]; let z:=Nt K w; change inner ℂ (M S p.b Ω.val) (M S p.b (L z))=_; rw [tsees]; exact amber M' S Ω hΩ w p.Λ h e -- argument order
lemma grain (h:M'.Warrant S Ω)(e:∀ b:Mink.Ray,Shelf S (magnet b))(v:List M'.Token): inner ℂ (L (Nt p w)) (L (Nt p v))=inner ℂ (L w) (L v):=by
 suffices he:∀ (x:List M'.Token)(y:List M'.Token), inner ℂ (L x) (L y)=Q ((x.map M'.reve).reverse++y) by
    let W:=travel M' p; rw [he,he,← show Nt p ((w.map M'.reve).reverse++v) = (((Nt p w).map M'.reve).reverse++(Nt p v)) from (by simp only [moved,List.map_append, List.map_reverse,List.map_map]; rw [show W ∘ M'.reve=M'.reve ∘ W from funext (travel_reveal M' p)]), M'.voyage S Ω hΩ]
    exact h; exact e -- Shelf from universe.Live. maybe add args
 intro x; induction x with
 | nil=> exact fun y=>rfl
 | cons i x ih=>
    intro y; unfold Ticket; rw [planeV,legPaid]; change inner ℂ (L x) (L (M'.reve i::y))= _; rw [ih]; simp
#print axioms amber
#print axioms bring
#print axioms grain
end Canopy
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
