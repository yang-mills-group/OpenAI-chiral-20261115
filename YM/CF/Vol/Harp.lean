import YM.CF.Vol.Snow
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03 Nacre
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Oriented Rows
variable (T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(s: Signed)(l:ℕ)
local notation "Ω"=>pulse (sol S T k x F l)
local notation "tK"=>Stores.till x
local notation "χ"=> choice s k
def FK(i:Twin f):=(fun z=>OrnG T F k s tK z i) ∘ Ω
-- keep jump corrections in η as in Appel, aff shift difference estimates later
def IK(i:Bond c):=(fun z=>OriG T F k s tK z i) ∘ Ω
def fX:Ark T F → Config G f:= Jazz T χ s ∘ Ω
def vX:Ark T F → Config G c:= Jade T χ s
def LX(i:Twin c):=fun z=> RiftL tK (fX T x F k s l z) (vX T F k s z) T χ i
def DX(i:Twin c):=fun z=> RiftD tK (vX T F k s z) T i
def XX(i:Twin c):=fun z=>T.Xn tK (vX T F k s z) i
def NX(i:Co c Gain):=fun z=> RiftN tK (vX T F k s z) T i
variable {x F T k s l}
lemma face_nice {v:ℝ}(p:K.Funds S T)(i:Twin c): XX T x F k s i 0=0:=by
 unfold XX vX Jade; rw [show facadeX G _=1 from by change facadeX G (0:Mast G c)=1; simp [facadeX],show pull s 0 (1:Config G c)=1 from (by funext i; simp [pull,Step.read])]; unfold Xn plotted; split
 · unfold shorten; have hg (j:ℕ): shortenTerm T.down (Stores.till x) S.patch.L.val (1:Config G c) i.1 j=0:=by unfold shortenTerm; split; simp [PathData.ellTerms,Work.F03.atSite_path,faceValue,square, travel, Step.read]; rfl
   simp_rw [tsum_congr hg]; exact tsum_zero
 · simp [shoot,faceValue,travel,Step.read,square]
structure Acres(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(s:Signed)(l:ℕ)(D:ℝ) : Prop where
 roof i: stance (FK T x F k s l i-gloss T x F k (s,.inl i)) D
 jamb i: stance (IK T x F k s l i-gloss T x F k (s,.inr i)) D
 letup i: stance (LX T x F k s l i) D
 nPole i: stance (NX T x F k s i) D
 dPole i: stance (DX T x F k s i) D
structure Well(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(s:Signed)(l:ℕ)(w:ℕ)(A:ℝ)(u:Ark T F):Prop where
 H i: Jet.Allows w (FK T x F k s l i) u A
 Tq i: Jet.Allows w (IK T x F k s l i) u A
 S i: Jet.Allows w (LX T x F k s l i) u A
 N i: Jet.Allows w (NX T x F k s i) u A
 P i: Jet.Allows w (XX T x F k s i) u A
 D i: Jet.Allows w (DX T x F k s i) u A
 Y i: Jet.Allows w (gloss T x F k i) u A
 E i: Jet.Allows w (fun y=>KissP (fX T x F k s l y) T i) u A
 C i: Jet.Allows w (fun y=>KissI (fX T x F k s l y) (vX T F k s y) (choice s k) i) u A
 Q i: Jet.Allows w (fun y=>KissQ (vX T F k s y) T i) u A
structure Tabac(T:Tube G S)(x:ℝ)(F:Forest S.ratio) (k:S.Choices)(s:Signed)(l:ℕ)(w:ℕ)(D A e:ℝ):Prop where
 -- kissJ
 funds:Acres T x F k s l D
 J(i:Slots S): gloss T x F k i 0=0
 H i : cFoot 3 (fun y=>KissP (fX T x F k s l y) T i)
 Tq i : cFoot 3 (fun y=>KissI (fX T x F k s l y) (vX T F k s y) (choice s k) i)
 P i : cFoot 3 (fun y=>KissQ (vX T F k s y) T i)
 B i: XX T x F k s i 0=0
 ears(u:Ark T F)(hu:‖u‖<e) : Well T x F k s l w A u
lemma paper {g:E→ B}{x:E}(h:Allows n g x C):Jet.Allows n g x C:= ⟨h.analytic.of_le le_top,h.norm_le⟩
-- prep self-growth allocation
lemma gum {g:E→B}{x:E×B}(h:Jet.Allows n g x.1 C)(ht:‖x‖ ≤ 1):Jet.Allows n (pulse g) x (1+Jet.composeCost n C 1):=by
 let P:=ContinuousLinearMap.snd ℝ E B; let Q:= ContinuousLinearMap.fst ℝ E B; let B:=Jet.composeCost n C 1; have hh:= (h.comp (f:=Q) (Jet.allows_linear (ContinuousLinearMap.norm_fst_le ..) ((norm_fst_le x).trans ht))); exact (Jet.allows_linear (x:=x) (L:=Q) (ContinuousLinearMap.norm_fst_le ..) ((norm_fst_le x).trans ht)|>.mono (le_add_of_nonneg_right hh.nonneg)).pair ((Jet.allows_linear (x:=x) (n:=n) (L:=P) (ContinuousLinearMap.norm_snd_le ..) ((norm_snd_le x).trans ht)).add hh)
-- port allocation
end YM.CF.Vol
