import YM.CF.Graph.Slay
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
variable {n:Side}
lemma face_z(U:Bkg N)(a: Hat)(s: Signed)(p:Face (Per N)):faceValue (pull s 0 (welt U a)) p=faceValue (pull s 0 U) p:=by
 let V:=wob N (fun i=> central^(a i).val); have he(x:Site N)(i j: Axis): travel V x (square i j)=1:=by
    have hp:= square_c x a U i j; rw [path_cent] at hp; exact mul_right_cancel (hp.trans (one_mul _).symm)
 let f(x:E):Prop:= x=1; have hf(x:E): f x⁻¹=f x:=propext inv_eq_one
 have hg(x u:E): f (u*x*u⁻¹)=f x:=propext (by
    constructor <;> intro g; change x=1; apply mul_left_cancel (a:=u); apply mul_right_cancel (b:=u⁻¹); simpa only [mul_one, mul_inv_cancel] using! g -- tune
    change x=1 at g; simp [g,f])
 have hh(x:Site N)(i j:Step): travel V x (oriented i j)=1:= (Lattice.price_shift_pos f V hf hg i j x).mpr (he ..)
 rw [faceValue,faceValue,travel_pull,travel_pull,path_cent]; change travel V _ _*_ =_; rcases p with ⟨x,⟨⟨i,j⟩,v⟩⟩; rw [show (square i j).map (fun x=> x.rotate s)=oriented ((posDir i).rotate s) ((posDir j).rotate s) from ?_,hh,one_mul] -- tune
 simp only [square,List.map_cons,List.map_nil,oriented, ←Step.rev_rotate,Step.rev_pos]
lemma zen(U:Bkg N)(a:Hat)(t:ℝ): flags t (welt U a)=flags t U:=by ext i; simp_rw [flags_spec,faceValue,square_c] -- tune
lemma choir (U:Bkg N)(h:Hat)(s:Signed)(x:Site N)(a:RG.Slot):a.atSite (pull s 0 (welt U h)) x=a.atSite (pull s 0 U) x:=by
 let W:=wob N (fun i=>central^(h i).val); have he(w:Walk)(i:Site N)(x:E):Commute x (travel W i w):=by induction w generalizing i with| nil=> exact Commute.one_right _ | cons z y ih=> exact Commute.mul_right (cent_v i h z x) (ih _)
 let y:= faceValue (pull s 0 U) (slotFace a x); rw [atSite_path,atSite_path,face_z,travel_pull,travel_pull,path_cent,← group.curvature_conjugate,← group.curvature_conjugate]; congr 1; let i:=affine s 0 x; let w:=a.walk.map (fun z=>z.rotate s); let v:=travel W i w; let q:=travel U i w; change v*q*y*(v*q)⁻¹=q*y*q⁻¹; rw [show v*q*y*(v*q)⁻¹=v*(q*y*q⁻¹)*v⁻¹ by group, ← (he w i (q*y*q⁻¹)).eq,mul_inv_cancel_right]
lemma choc(R: GramM n)(a:Hat)(V:Pane n):R.path.inChannels R.funds R.p R.beta (welt V a)=R.path.inChannels R.funds R.p R.beta V:=by
 unfold inChannels; apply congrArg; apply sum_congr rfl; intro s _; let U:= pull s 0 (welt V a); let X:= pull s 0 V; change R.path.principal _ _ _ U= _; have h:flags R.p.threshold U=flags R.p.threshold X:=by ext i; simp_rw [flags_spec]; unfold U X; simp_rw [face_z]
 have hp {k:ℕ}(W:ℕ→Atom SU.group k)(i:Site (More n)): atomSeries W R.p U i=atomSeries W R.p X i:=tsum_congr fun x=> (by
    by_cases e:Healthy R.p.threshold ((W x).footprint i) U
    · have he:Healthy R.p.threshold ((W x).footprint i) X:=by unfold Healthy at *; rwa [←h] -- tune
      rw [Atom.placed,Atom.placed,masked_eq _ _ _ _ e,masked_eq _ _ _ _ he]; unfold Atom.unmasked U X; simp_rw [choir]
    rw [Atom.placed, Atom.placed, masked_ne _ _ _ _ e,masked_ne _ _ _ _ (show ¬Healthy _ _ X from ?_)]; unfold Healthy at *; rwa [←h]) -- tune
 unfold PathData.principal; have hx(i:Face (Per (More n))):R.path.baseTerm R.funds R.p U i=R.path.baseTerm R.funds R.p X i:=by
    unfold baseTerm U X; simp only [face_z,kept,ell,ellTerms,choir] -- tune
 change R.beta*((∑ i,R.path.baseTerm R.funds R.p U i)+_)+_= R.beta*((∑ i,R.path.baseTerm R.funds R.p X i)+_)+_; simp_rw [hx,hp]; rfl
end YM.CF.Graph
