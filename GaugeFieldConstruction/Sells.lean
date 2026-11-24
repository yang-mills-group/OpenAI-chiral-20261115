import GaugeFieldConstruction.Bank
/-!
# Touch any actual input to these programs
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Calibration.RawBank
open Gap Cauchy Row Phys Function Submodule U1 Flux One Stage Wide Stage.Cell One.Lamp Floor
open Matter (Slot FlavorIndex)
open scoped BigOperators Topology ContDiff
variable {K : Dollars} {Ω : Rotors}

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (l m : Slot) (a : ℂ) (V : Bool→ℂ) (p : Course K) (h : Toll K Ω.val)

def GC (a : ℂ) (K : Dollars) (Ω : Rotors) {R} (d : Mint recG R Conj.cG α) (T : Cell α) := ∀ i, (gloG (gStress a)).Touch K a (graph_g (d.issue (ket i)).val) (graph_g (d.issue (T.beta Ω (ket i))).val)
lemma glueG {R U} {d : Mint recG R Conj.cG α} {e : Mint recG U Conj.cG β} {T : Cell α} {P : Cell β} (h : GC a K Ω d T) (u : GC a K Ω e P): GC a K Ω (d.cup e) (T.sum P) := by
  rintro (i|i)
  · rw [Mint.paid_at, input1]; change Touch _ _ _ (graph_g (d.q _)) (graph_g (jet _ (leftU _)))
    rw [monop, ← d.paid_at i]; exact h i
  rw [Mint.paid_at,input2]; change Touch _ _ _ (graph_g (e.q _)) (graph_g (jet _ (rightU _)))
  rw [monopol,← e.paid_at i]; exact u i
include p h
lemma shelG (i) : GC a K Ω (DeckG i) (gCard i) := by
  have he : GC a K Ω G4b PG:=fun i=>by rw [G4b.paid_at]; exact crown p h a i
  have hp : GC a K Ω G5b PG1:=fun i=>by rw [G5b.paid_at]; exact crossV p h a i
  cases i
  · exact (show GC a _ _ (stub recG _) (Still Empty) from fun i : Empty=> i.elim)
  · exact he
  exact glueG _ he hp
lemma Go (d) (x : J (BoxG d)) : Touch (gloG (gStress a)) K a (graph_g ((DeckG d).issue x).val) (graph_g ((DeckG d).issue ((gCard d).beta Ω x)).val) := by
  induction x using Finsupp.induction_linear with
  | zero=> simp [emptyT]
  | add b c t u => simp only [map_add,Submodule.coe_add]; exact Lamp.plus _ p t u
  | single i t=> rw [show Finsupp.single i t=t • ket i from by simp [ket]]; simp only [map_smul,Submodule.coe_smul_of_tower]; exact Lamp.wish _ (shelG a p h d i) _ -- coe lemma?
omit p h
def FC (c m : Slot) (K : Dollars) (Ω : Rotors) (V : Bool→ℂ) {R} (d : Mint ph R Conj.cF α) (T : Cell α) := ∀ i,(d.q i,(d.issue (T.beta Ω (ket i))).val)∈ready V c m K
lemma glueF {R U} {d : Mint ph R Conj.cF α} {e : Mint ph U Conj.cF β} {T : Cell α} {P : Cell β} (v : FC l m K Ω V d T) (u : FC l m K Ω V e P):FC l m K Ω V (d.cup e) (T.sum P):=by
  rintro (i|i)
  · rw [input1]; change (_,jet _ (leftU _))∈ _; rw [monop]; exact v i
  rw [input2]; change (_,jet _ (rightU _))∈_; rw [monopol]; exact u i
include p h
lemma shelF (i): FC l m K Ω V (DeckF i) (fCard i):= by
  have he : FC l m K Ω V FB UnitV:= fun i=>Bc p h V i
  have hp : FC l m K Ω V F1 PT1:=fun i=> Tc p h V i
  have hw := glueF l m V he hp
  cases i
  · exact he
  · exact hw
  exact glueF l m V hw (show FC _ _ _ _ _ F2 PT2 from fun i=> Vc p h V i)
lemma Fo (d) (k : FlavorIndex) (x : J (BoxF d)) : Touch (gloF (fStress V)) K (V k.1) (tiap k ((DeckF d).issue x).val) (tiap k ((DeckF d).issue ((fCard d).beta Ω x)).val) := by
  induction x using Finsupp.induction_linear with
  | zero=> simp [emptyT]
  | add b c t u=> simp only [map_add,Submodule.coe_add]; exact Lamp.plus _ p t u
  | single i t=> rw [show Finsupp.single i t=t • ket i from by simp [ket]]; simp only [map_smul, Submodule.coe_smul_of_tower]; apply wish; rw [Mint.paid_at]; exact phase p V _ _ (fun l m=> shelF l m V p h d i) k

omit p h

def xpay (k : FlavorIndex) (d : Floor): J (BoxX d) →ₗ[ℂ] J Trip:= tuap k ∘ₗ (SX d).subtype ∘ₗ (DeckX d).issue
def scratch (A : Rotors) (d : Floor) (a b : ℂ): Module.End ℂ (J (BoxX d)):=a • (xCard d true false |>.beta A)+ b • (xCard d false true |>.beta A)
lemma cash (k d z) : xpay k d z=tuap k ((DeckX d).issue z).val := by rw [xpay,LinearMap.comp_apply,LinearMap.comp_apply,Submodule.subtype_apply]
lemma pd (i : BoxX five) : (DeckX five).q i=Wide.log i:= rfl
lemma xid (k i) : xpay k five (ket i)=tuap k (Wide.log i) := by rw [cash,Mint.paid_at,pd]
lemma ars (Ω k i b) : xpay k five (scratch Ω five a b (ket i))=tuap k (a • (jet Wide.log (mixB i Ω))+ b • jet Wide.log (mixL i Ω)) := by
  rw [cash, scratch]; simp only [LinearMap.add_apply,LinearMap.smul_apply]; -- then turn pieces without moving tuap
  have h (u v : J (BoxX five)):((DeckX five).issue (a • u+b • v)).val=a • jet Wide.log u+b • jet Wide.log v := by
    rw [map_add,map_smul,map_smul, Submodule.coe_add,Submodule.coe_smul_of_tower,Submodule.coe_smul_of_tower]; rfl
  rw [h]; -- avoid rfl on deep types
  have hu (i : BoxX five) : (xCard five true false).beta Ω (ket i)=mixB i Ω:=rfl
  have ht (i : BoxX five) : (xCard five false true).beta Ω (ket i)=mixL i Ω:=rfl
  -- ill types maybe cast.
  rw [hu,ht]
lemma Xout {χ : E4→ℝ} {x y : E4} (Ω : Rotors) (c : Chassis x y χ) (k : FlavorIndex) (d : Floor) (z : J (BoxX d)) : Latch (gloX (fStress V) (gStress a)) χ (soar Ω x) x y (xpay k d z)
    (xpay k d (scratch Ω d a (V k.1) z)) := by
  induction z using Finsupp.induction_linear with
  | zero=> simp; exact mints _
  | add u v p q => simp only [map_add]; exact Lamp.summer _ (soarC Ω x).toCourse c p q
  | single i t=>
    rw [show Finsupp.single i t=t • ket i from by simp [ket],map_smul (xpay k d),map_smul, map_smul (xpay k d)]; apply Lamp.coins
    cases d
    · exact (show Empty from i).elim
    · exact (show Empty from i).elim
    rw [ars,xid]; exact mixed_pay Ω i a V k c
end YM.GaugeFieldConstruction.Calibration.RawBank
