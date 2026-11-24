import YM.SU5.FiniteGaugeData.Nine.NectarP
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Chaperone Heat Afterglow.Hierarchy.Eight Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
set_option quotPrecheck false
open Window.Pivot Tint
variable (o:Cover){N:Side}
local notation "Μ"=> Single N
open Fock Fock.Brique
local notation "H₀"=> (polarQ o)
open Nacre
abbrev beamAngle : PlaqAxes:=⟨(0,3),by decide⟩
abbrev mainF:Face ℤ:= (o,beamAngle)
abbrev flipF:Face ℤ:= (o-step 0,beamAngle)
def pocket : Finset (Face ℤ):= {mainF o,flipF o}
private abbrev yagi (a:Axis)(f:Face ℤ) : Face ℤ := Face.send (Signed.mirror a) (2 • (o a • step a)) f
private lemma roll(y:Cover)(a j:Axis) : (Pivot.pole a o).motion (o+y) j=if a=j then o j-y j else o j+y j:=by
 unfold Pivot.pole; rw [fling_move]; by_cases h:a=j; · simp only [h, ↓reduceIte, Pi.add_apply]; ring
 simp only [h,↓reduceIte, Pi.add_apply]
private lemma roll_z : (Pivot.pole 0 o).motion o=o:= by nth_rw 2 [← add_zero o]; ext i; rw [roll]; by_cases h:(0:Axis)=i<;>simp [h]
private lemma roll_v : (Pivot.pole 0 o).motion (o-step 0)=o+step 0:= by
 rw [sub_eq_add_neg]; ext i; rw [roll]; by_cases h:(0:Axis)=i; · simp [h]
 simp [h,Ne.symm h]
private lemma roll' (a i:Axis)(x:Cover)(p:o a=x a): (Pivot.pole a o).motion x=x:=by ext i; by_cases h:a=i<;> simp only [Pivot.pole,fling_move,h, ↓reduceIte]; rw [h] at p; linarith -- no rfl? tune
variable (y:Cover)
lemma yagi_0 : yagi o 0 (mainF y)= ((Pivot.pole 0 o).motion y-step 0,beamAngle):=by
 apply Prod.ext; unfold yagi Face.send Face.lower atFace; change _ + (if (((posDir 0).rotate (Signed.mirror 0)).neg) then ((posDir 0).rotate _).vec else 0)+ (if ((posDir 3).rotate (Signed.mirror 0)).neg then _ else _)=_
 · rw [if_pos (by decide),if_neg (by decide),show ((posDir 0).rotate (Signed.mirror 0))=negDir 0 from rfl, Step.vec_neg, sub_eq_add_neg,add_zero]; rfl
 rfl -- can't decide with o? snd reducible. use rfl likely Fin.min computed
lemma yagi_other(a:Axis)(h:a≠0)(p:a≠3) : yagi o a (mainF y)= ((Pivot.pole a o).motion y,beamAngle):=by
 have he {j:Axis}(h:a≠j) : (posDir j).rotate (Signed.mirror a)=posDir j := by simp [Signed.mirror,posDir,h,Step.rotate]
 apply Prod.ext; unfold yagi Face.send Face.lower atFace mainF beamAngle; dsimp only; rw [he h,he p,if_neg (by decide),if_neg (by decide),add_zero,add_zero]; rfl; rfl
lemma yagi_pay (a:Axis)(V:LinksC)(x:Face ℤ) : SU.group.chord (faceValue (jumpsC o a V) x) = SU.group.chord (faceValue V (yagi o a x)):= Face.send_price V _ _ _ _ SU.group.chord_inv fun i k=> SU.group.chord_conj k i
lemma faro(V:LinksC): SU.group.chord (faceValue (leaps o V) (mainF o))=SU.group.chord (faceValue V (flipF o)) ∧ SU.group.chord (faceValue (leaps o V) (flipF o))=SU.group.chord (faceValue V (mainF o)):=by
 have he(a:Axis)(p:a≠0)(h:a≠3) : yagi o a (flipF o)=flipF o:=by unfold flipF; change yagi o a (mainF (o-step 0))=_; rw [yagi_other o _ a p h, roll' o a a (o-step 0) (by simp [p.symm,p])]
 have hz(a:Axis)(p:a≠0)(h:a≠3): yagi o a (mainF o)=mainF o:=by rw [yagi_other o _ a p h,roll' o a a o rfl]
 have h1: yagi o 0 (mainF o)=flipF o:= by rw [yagi_0 o o,roll_z]
 have h2: yagi o 0 (flipF o)=mainF o:=by rw [show flipF o=mainF (o-step 0) from rfl, yagi_0 o (o-step 0),roll_v,add_sub_cancel_right]
 unfold leaps; simp_rw [yagi_pay,h1,h2, he 1 (by decide) (by decide),hz 1 (by decide) (by decide),he 2 (by decide) (by decide),hz 2 (by decide) (by decide)]; -- tune h1 h2 repeated rewriting in `simp_rw`
 exact ⟨trivial,trivial⟩
lemma dual_angle (b:ℝ)(x:LinksC): amber b (pocket o) (leaps o x)=amber b (pocket o) x:=by
 unfold pocket amber; have he: mainF o≠flipF o:=by intro v; have hx:= congr_fun (congrArg Prod.fst v) 0; change o 0= (o-step (0:Axis):Cover) 0 at hx; simp at hx; omega
 simp_rw [prod_insert (fun u=> he (Finset.mem_singleton.mp u)),prod_singleton,faro o x|>.1,faro o x|>.2]; rw [mul_comm]
private lemma flip_site : o-step (0:Axis)∈ Quest.scape o 1:=by
 refine sap_box.mpr ?_; intro k; simp only [Pi.sub_apply]; by_cases h:k=(0:Axis) <;> (simp [h]<;> omega)
private lemma anglesites {p:Face ℤ}(h:p∈ pocket o): p.1∈Quest.scape o 1:=by
 rcases mem_insert.mp (show p∈insert (mainF o) {flipF o} from h) with h|t
 · rw [h]; exact sap_here o 1
 rw [mem_singleton.mp t]; exact flip_site o
private lemma axlands (A:Finset (Face ℤ))(r m:ℕ)(t:m+4≤r)(h:∀ i∈A,i.1∈Quest.scape o m) : carpet A⊆ Quest.scape o r:=by
 intro i x; obtain ⟨a,u,v⟩:= mem_biUnion.mp x; let P:= square a.2.val.1 a.2.val.2; have hv:i∈ visits a.1 P:=List.mem_toFinset.mp v
 have he:m+P.length=m+4:=rfl; have hp : i∈ Quest.scape o (m+P.length):= vision_box (h a u) hv; rw [he] at hp; apply scape_mono t hp
lemma dual_space {r:ℕ}(p:5≤ r): carpet (pocket o) ⊆ Quest.scape o r:= axlands o (pocket o) r 1 p (fun _ h=> anglesites o h)
variable (K:Calibration)
lemma pageP_scale (r:ℝ)(x:Family K): pageP o K (shineB r (pocket o) K*x)=shineB r (pocket o) K*pageP o K x:=by
 have he (f g:Family K) : pageP o K (f*g)= pageP o K f* pageP o K g:=funext fun i=>funext fun x=> (by change twist (quantU (prepU (polarQ o) 1 inert (K.c i))) (_*_) = _ ; rw [map_mul]; rfl)
 let Y:=shineB r (pocket o) K; rw [he]; congr 1; funext m x'; change imageQ H₀ _ (Y m (rollR H₀ x'))=_; unfold Y shineB scalar; rw [imageQ, twist_scalar,imageOne]; dsimp only [Function.comp_apply,rollR,Prod.map]; rw [leaps_here,dual_angle]
lemma Stall.funds {A:Finset Cover}{σ:Window.Family}{x:Family K} (t:Stall K A σ x){S:Finset (Face ℤ)}(p:carpet S ⊆ A) (r:ℝ) : Stall K A σ (shineB r S K*x):=by induction t with
 | off=> rw [mul_zero]; exact .off
 | haloP v=> exact .haloP (shine_spec r S K v p)
 | add _ _ a b=> rw [mul_add]; exact .add a b
 | scale _ _ a=> rw [Algebra.mul_smul_comm]; exact .scale a _
end YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP.pageP_scale
