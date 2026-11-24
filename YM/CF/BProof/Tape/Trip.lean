import YM.CF.BProof.Tape.Walk
import YM.CF.BProof.Wick.Liquid

/-! Budget book for every such physical datum (of original argument sizes n≥k,
rates kept uniform even once Mark schedule purchased later than here). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tape
open Function Filter Fock Finset Branch Stint Align Wick Hearth Spin Tenant Lat Lattice Tulip Cube Fig
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r δ c v η:ℝ}{N:Side}{P: Ready j a b l r}{F:Core j a b l r N}(h:Age P F δ)
def kiln (h:Age P F δ)(c v η:ℝ):Feet N (Loft F δ c v η) := Hearth.usher (Tape.vacuum h v c) _ (fun g x p=>dream_t h _ p)
lemma gate {p:Pay}{A:Raw (InRoad F δ c) (Single N)}(q:Earn p (h.beam c).mark (h.beam c).mark A)(v η:ℝ): Earn p (Tape.kiln h c v η).mark (Tape.kiln h c v η).mark (fun x=>A x.val.1):= (usherG ..).mark ((Feet.doubleSkid (h.beam c) Skein.move Skein.toll (fun i x y=> Skein.toll_pos i x y)).mark q)
abbrev carried (x:InRoad F δ c):= x.val.1.val
abbrev cutX (u:Bool)(x:InRoad F δ c):= bandCut x.val.2 u
def purseT(x:InRoad F δ c):= purse (F.wind (carried x)) (F.θ (carried x) 1) (cutX true x) (cutX false x)
abbrev piF(x:InRoad F δ c):= entryP (F.θ (carried x) 1) (cutX true x) (cutX false x)
abbrev view (x:Loft F δ c v η)(k:Key):= path x.val k
def billR(x:Loft F δ c v η):=periodQ (piF x.val.1) (view x (false,false) 1)
def labelR : Raw (Loft F δ c v η) (Single N) := rollF (fun x=> F.upright (carried x.val.1)) (fun x=>F.wind (carried x.val.1)) (fun x=> cutX true x.val.1) (fun x=>cutX false x.val.1) (fun x=> view x (true,false)) (fun x=> view x (false,false)) (fun x=> view x (true,true)) (fun x=> view x (false,true))
def driftW(x:Loft F δ c v η):= let y:= x.val.1; Double.cern (F.θ (carried y) 1) (cutX true y) (cutX false y) (view x (false,false) 1)
def keyF(x:Loft F δ c v η):= lumpLog (F.upright (carried x.val.1)) (F.wind (carried x.val.1)) (view x (true,false)) (view x (false,false)) (view x (true,true)) (view x (false,true)) (cutX true x.val.1) (cutX false x.val.1)
abbrev solid (x: Loft F δ c v η):= SumK (F.upright (carried x.val.1)) (F.wind (carried x.val.1)) (view x (true,false)) (view x (false,false)) (view x (true,true)) (view x (false,true)) (cutX true x.val.1) (cutX false x.val.1)
def Tickets (k:Pay)(P:Ready j a b l r)(δ c v η:ℝ)(F:Core j a b l r N) (h:Age P F δ): Prop:= let f:=h.beam c; let g:=Tape.kiln h c v η; Earn k f.mark f.mark purseT ∧ Earn k g.mark g.mark billR ∧ Earn k g.mark g.mark labelR ∧ Earn k (Double.dye g.mark).reverseV (Double.dye g.mark) driftW ∧∀ x:Loft F δ c v η,solid x ∧ keyF x=((↑((purseT x.val.1).trace.re+(billR x).trace.re)):ℂ)+zen (labelR x).trace
lemma usherParam {D:Type}[TopologicalSpace D](b: Feet N D)(w:D→Prop)(k:∀ g x,w x→w (b.st.drive g x)){v:Pay}{A:Raw (D × Time) (Single N)}(h:Earn v (straw b.mark) (straw b.mark.reverseV) A): let t:=usher b w k; Earn v (straw t.mark) (straw t.mark.reverseV) (fun x=> A (x.1.val,x.2)):=by intro t; let B:=Subtype w; exact h.restrict (fun i:B×Time=>(i.1.val,i.2)) ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) rfl rfl (fun x i j=>le_rfl) id (fun g x=>rfl) rfl rfl
lemma sparkPrice (v:ℝ)(p:1≤v): ∃ q:Pay, ∀ {j a b l r δ c η N}{P:Ready j a b l r}{F: Core j a b l r N}(h:Age P F δ)(g:Key), let T:= (Tape.kiln h c v η).mark; Earn q (straw T) (straw T.reverseV) (divY (fun x=>view x g)) :=by
 obtain ⟨q,S⟩:= Skein.earns p; refine ⟨q,?_⟩; intro j a b l r d c u n P F h g k; let t:= h.beam c; let y:= Skein.hall t v
 exact usherParam y _ (fun g x p=> dream_t h g p) (S t g)
end YM.CF.BProof.Tape
