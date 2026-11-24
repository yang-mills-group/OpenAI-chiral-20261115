import YM.SU5.FiniteGaugeData.Trigonal.Pepper
import YM.SU5.FiniteGaugeData.Stent.Dale
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "X"=> Trigo.Chamber true -- Window opened
local notation "Y₀"=> Trigo.Chamber false
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
variable {N: Side}{R:Patch}
local notation "ℱ"=> FC (Single N)
abbrev TF (N:Side) (b:Bool): Set (FC (Single N)) := fun P=> Fine (Tset N) univ b P
lemma TCommute {a:Bool}{f g:FC (Single N)} (h:f∈TF N false) (p:g∈TF N a) : Commute f g:= by unfold Commute SemiconjBy; have h:= (show Fine .. from h).sign_com p; simpa [Sector.grainB] using h -- syntax binder fine dots?
lemma Tprod(f:Fin n→FC (Single N))(p:∀ i,f i∈TF N false): rollF f∈TF N false:=by induction n with| zero=> unfold rollF; rw [List.ofFn_zero,List.prod_nil]; exact Fine.one| succ n ih=> unfold rollF; rw [List.ofFn_succ,List.prod_cons]; exact Fine.grow (show Fine _ _ false _ from p 0) (ih (fun i=>_) (fun i=>p i.succ)) -- elab implicit
lemma wageH(x:X)(a:SU.Slot):withinM (Tset N) (quantum N x a):=(by have h:= LF (N:=N) x a; rw [touchP] at h; exact h)
lemma wageL(y:Y₀)(a:SU.Slot):withinM (Tset N)ᶜ (quantum N y a):=by have h:= BF (N:=N) y a; rw [touchP,←dim_cut] at h; exact h
lemma Upper(x:X)(a:SU.Slot): create (quantum N x a)∈TF N true:=fine_create _ (wageH x a) (within_univ _)
lemma Lower(y:Y₀)(a:SU.Slot):Fock.remove (quantum N y a)∈TF N true:=fine_remove _ (wageL y a) (within_univ _)
variable (f:Fin n→Trigo.Chamber true)(g':Fin n→Trigo.Chamber false)
abbrev Blend (N:Side)(p:SU.Slot × Fin n):=create (quantum N (f p.2) p.1)*Fock.remove (quantum N (g' p.2) p.1)
lemma BlendP(i:Υ n): Blend f g' N i∈TF N false:=Fine.grow (Upper (f i.2) i.1) (Lower (g' i.2) i.1)
lemma TorqueP : TextK f g' N ∈ TF N false:= Tprod _ (fun i=>BlendP f g' _)
abbrev RingRose(n:ℕ): List (SU.Slot × Fin n) := List.ofFn ⇑(collar n)
lemma TextRibbon : TextK f g' N=((RingRose n).map (Blend f g' N)).prod:=by unfold RingRose; rw [List.map_ofFn]; rfl
section
abbrev peel (n:ℕ) (a: SU.Slot × Fin 1): SU.Slot × Fin (n+1):= (a.1,0)
abbrev veins (n:ℕ) (b:SU.Slot × Fin n):SU.Slot × Fin (n+1):= (b.1,b.2.succ)
lemma rose_mem (p:Υ n) : p∈ RingRose n:=List.mem_ofFn.mpr ((collar n).surjective p)
lemma petal : (RingRose n).Nodup:=List.nodup_ofFn.mpr (collar n).injective
lemma concord : List.Perm (RingRose (n+1)) ((RingRose n).map (veins n) ++ (RingRose 1).map (peel n)):=by
 refine (List.perm_ext_iff_of_nodup petal (List.nodup_append.mpr ?_)).mpr ?_
 · refine ⟨petal.map ?_, petal.map ?_, ?_⟩; · exact fun i j p=>Prod.ext (Prod.mk.inj p).1 ((Fin.succ_injective n) (Prod.mk.inj p).2)
   · exact fun i j p=>Prod.ext (Prod.mk.inj p).1 (Subsingleton.elim ..)
   intro a h b k; obtain ⟨x,_,rfl⟩:= List.mem_map.mp h; obtain ⟨y,_,rfl⟩:= List.mem_map.mp k; exact fun p=> Fin.succ_ne_zero _ (congrArg Prod.snd p)
 rintro ⟨x,i⟩; simp only [rose_mem,List.mem_append,List.mem_map,true_and,true_iff]; refine Fin.cases ?_ ?_ i; · exact Or.inr ⟨(x,0),rfl⟩
 exact fun i=> Or.inl ⟨(x,i),rfl⟩ -- tune p′
abbrev roseone{A:Type*}(x:A): Fin 1→ A:= fun _=> x
lemma Bramble (f: Fin (n+1)→ X)(g':Fin (n+1)→ Y₀) : TextK f g' N= TextK (f ∘ Fin.succ) (g' ∘ Fin.succ) N* TextK (roseone (f 0)) (roseone (g' 0)) N:=by
 simp_rw [TextRibbon]; let g:= Blend f g' N; rw [(concord.map g).prod_eq',List.map_append,List.prod_append,List.map_map,List.map_map]; rfl
 refine List.pairwise_map.mpr (List.pairwise_iff_getElem.mpr fun i j h e _=> TCommute (BlendP f g' _) (BlendP f g' _))
#print axioms Bramble
end
-- annihilator ringA.pair.
variable {Z:FC (Single N)}
private lemma Heavy {n:ℕ} (f:Fin n→ FC (Single N))(h:∀ i,f i∈TF N false)(e:Z∈TF N true)(i:Fin n)(z:f i*Z=0):rollF f* Z=0:= by
 induction n with
 | zero=>exact i.elim0
 | succ n ih=> unfold rollF; rw [List.ofFn_succ,List.prod_cons]; let t:= f ∘ Fin.succ; let H(x:Fin n):= h x.succ; change f 0* rollF t*Z=_; refine Fin.cases ?_ ?_ i z; · intro p; rw [mul_assoc,(TCommute (Tprod t H) e).eq,←mul_assoc,p,zero_mul]
               exact fun j p=> (mul_assoc ..).trans ((congrArg (fun a=> f 0*a) (ih t H j p)).trans (mul_zero _)) -- issues dependent i rec induction? `i` `z` maybe not motive binder. tried
private lemma JetLag (p:Z∈TF N true):Z*Z=0:=by
 have he: Z*Z= -(Z*Z):=by simpa [Sector.grainB] using (show Fine _ _ true _ from p).sign_com (show Fine .. from p); -- met θ ambigu
 exact (smul_eq_zero_iff_right (by norm_num:(2:ℂ)≠0)).1 ((two_smul ℂ _).trans (eq_neg_iff_add_eq_zero.mp he)) -- high
lemma hanky (a: SU.Slot)(e: Fin n): TextK f g' N*create (quantum N (f e) a)=0:=by
 let x:Υ n:=(a,e); let w:= Upper (N:=N) (f e) a; let y:=Lower (N:=N) (g' e) a; let t:=collar n; refine Heavy (Blend f g' N ∘ ⇑(collar n)) (fun i=>BlendP f g' _) w (t.symm x) ?_; let v:= create (quantum N (f e) a); let W₁:= Fock.remove (quantum N (g' e) a);
 have hp:W₁*v= -(v*W₁):= by simpa only [Sector.grainB,Bool.and_true,ite_true,neg_smul,one_smul] using (show Fine _ _ _ _ from y).sign_com w
 rw [comp_apply,show (collar n) (t.symm x)=x from t.apply_symm_apply x]; change v*W₁*v=0; rw [mul_assoc,hp,mul_neg,←mul_assoc, JetLag w,zero_mul,neg_zero] -- w he
lemma tiptoe (a:SU.Slot)(e:Fin n):TextK f g' N *Fock.remove (quantum N (g' e) a)=0:=by
 let x:Υ n:=(a,e); let y:=Lower (N:=N) (g' e) a; let t:=collar n; refine Heavy (Blend f g' N ∘ ⇑(collar n)) (fun i=>BlendP f g' _) y (t.symm x) ?_; rw [comp_apply,show (collar n) (t.symm x)=x from t.apply_symm_apply x]; unfold Blend; rw [mul_assoc,JetLag y,mul_zero]
#print axioms hanky
#print axioms tiptoe
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
