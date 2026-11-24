import GaugeFieldConstruction.Periscope
import GaugeFieldConstruction.Hindu
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
variable {c f: Side}{G:Ratio c f}{M:Male}{A:Site f}{Q H: Op (Single f)}{o:Skye.Seat f}{h b a p:ℝ}{k n m:ℕ}{X:SM f→ ℝ}
structure Rode(o:Skye.Seat f)(C:ℝ)(E:SM f→ ℝ)(Q: Op (Single f)) : Prop where
 sent:SentK o Q
 cost(i:SM f):‖Q i.1 i.2‖ ≤ C* E i
lemma Rode.null (x:∀ i,0≤ X i)(h:0≤p):Rode o p X 0:=⟨fun i j v=> False.elim (v rfl),fun i=>by simp only [Matrix.zero_apply,norm_zero]; exact mul_nonneg h (x i)⟩
lemma Rode.addH(u:Rode o a X Q)(v:Rode o b X H):Rode o (a+b) X (Q+H):=by
 refine ⟨fun i j h=>?_,fun i=>?_⟩ -- tune
 · by_cases he: Q i j=0; · apply v.sent _ _; rintro k; rw [Matrix.add_apply,k,he,add_zero] at h; contradiction
   exact u.sent _ _ he
 rw [Matrix.add_apply, add_mul]; exact (norm_add_le ..).trans (add_le_add (u.cost i) (v.cost i))
lemma Rode.liftH (u:Rode o a X Q)(t: a≤ b)(p:∀ i,0≤X i): Rode o b X Q:= ⟨u.sent,fun i=>(u.cost i).trans (mul_le_mul_of_nonneg_right t (p i))⟩
lemma Rode.scaleH (u:Rode o a X Q)(r:ℝ): Rode o (‖r‖*a) X (r • Q):=⟨fun i j p=>u.sent _ _ (fun he=>p (by change r • Q i j=_; rw [he,smul_zero])),fun i=>by change ‖r • Q i.1 i.2‖≤_; rw [norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (u.cost i) (norm_nonneg _)⟩
lemma winP_add(o:Skye.Seat f)(M:Male) (h:ℝ) (X Y:Op (Single f)) : winJ o M h (X+Y)= winJ o M h X+winJ o M h Y:=by
 apply (tab M (X+Y)).unique ; refine ((tab (o:=o) (h:=h) M X).joinK (tab M Y)).equal (Eventually.of_forall fun i=>?_)
 simp only [Pi.add_apply,TabX,streamF,hill_Z,Matrix.add_apply,mul_add,map_add,add_mul,sum_add_distrib]
lemma winP_scale(o:Skye.Seat f)(M:Male) (h:ℝ)(p:ℝ)(X:Op (Single f)) : winJ o M h (p • X)= p • winJ o M h X:=by
 let P:=winJ o M h X; let Q:=TabX o M h X; let L:=p • ContinuousLinearMap.id ℝ Pal; rw [show p • _=postF P L from ?_]; swap -- might rewrite lhs.Motive fixed.
 · apply Prod.ext; rfl; apply Prod.ext; exact ContinuousLinearMap.ext fun _=>rfl; exact Subtype.ext (ContinuousLinearMap.ext (fun _=>ContinuousLinearMap.ext (fun _=>rfl)))
 apply (tab M _).unique; refine ((tab (o:=o) (h:=h) M X).geomF L).equal (Eventually.of_forall fun i=>?_) -- local
 change p • TabX o M h X i= _; simp only [TabX,streamF,hill_Z,Matrix.smul_apply,mul_smul_comm,map_smul,← Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]
lemma winP_zero(o:Skye.Seat f)(M:Male) (h:ℝ): winJ o M h 0=0:=by simpa only [zero_smul] using winP_scale o M h 0 0
lemma quote_add (u:quote_B M Q o h k)(v:quote_B M H o h k): quote_B M (Q+H) o h k:= by unfold quote_B; rw [winP_add]; exact ⟨fun p=>by change _+_= _; rw [u.u p,v.u p,add_zero],fun p=>by change _+_= _; rw [u.v p,v.v p,add_zero],fun p=>by change _+_= _; rw [u.q p,v.q p,add_zero]⟩ -- tune
lemma quote_scale (u:quote_B M Q o h k)(t:ℝ): quote_B M (t • Q) o h k:=by unfold quote_B; rw [winP_scale]; exact ⟨fun p=>by change t • _ =_; rw [u.u p,smul_zero],fun p=>by change t • _ =_; rw [u.v p,smul_zero],fun p=>by change t • _ =_; rw [u.q p]; exact Subtype.ext (ContinuousLinearMap.ext (fun i=> ContinuousLinearMap.ext (fun j=> smul_zero t)))⟩
lemma quote_none (h:ℝ)(o:Skye.Seat f)(M:Male)(p:ℕ) :quote_B M 0 o h p:=by unfold quote_B; rw [winP_zero]; exact ⟨fun _=>rfl,fun _=>rfl,fun _=>rfl⟩
abbrev need (p:ℕ):ℕ:= p-2 -- either ≤1 when p≤3
structure Archive (M:Male)(k:ℕ)(o:Skye.Seat f)(h b C:ℝ)(X:SM f→ℝ)(P:Op (Single f)):Prop where
 bill:∃ U V R,P=U+V+R∧ Rode o C X U ∧ Rode o (C*b^(k-need k)) X V ∧ Rode o (C*b^k) X R ∧ quote_B M U o h k ∧ quote_B M V o h (need k)
lemma Archive.null (h':0≤ b)(p₀:0≤p)(u:∀ i,0≤X i):Archive M k o h b p X 0:= by -- tune unknown h''
 refine ⟨0,0,0,by simp,Rode.null u p₀,Rode.null u (by positivity), Rode.null u (by positivity),quote_none ..,quote_none ..⟩
lemma Archive.fuse {r t:ℝ}(v:Archive M k o h b r X Q)(p:Archive M k o h b t X H):Archive M k o h b (r+t) X (Q+H):=by
 obtain ⟨U,V,R,a,f,l,e,h,v⟩:=v.bill; obtain ⟨U',V',R',g,t,k,p,c,h'⟩:=p.bill
 refine ⟨U+U',V+V',R+R',?_,f.addH t,?_,?_,quote_add h c,quote_add v h'⟩; · rw [a,g]; abel
 · rw [add_mul]; exact l.addH k
 rw [add_mul]; exact e.addH p
lemma Archive.weaken {r t:ℝ}(v:Archive M k o h b r X Q)(p:r ≤ t)(q:0≤ b)(r:∀ i,0≤X i):Archive M k o h b t X Q:=by obtain ⟨U,V,R,h,f,l,e,t,h'⟩:=v.bill; exact ⟨U,V,R,h,f.liftH p r,l.liftH (mul_le_mul_of_nonneg_right p (pow_nonneg q _)) r, e.liftH (mul_le_mul_of_nonneg_right p (pow_nonneg q _)) r,t,h'⟩
lemma Archive.pay₁ (p:Rode o a X Q)(u:quote_B M Q o h k)(d:0≤b)(v:0≤a) (g:∀ i,0≤X i): Archive M k o h b a X Q:= ⟨Q,0,0,by simp,p,Rode.null g (by positivity), Rode.null g (by positivity),u,quote_none ..⟩
lemma Archive.pay₂ (p:Rode o (a*b^(k-need k)) X Q)(u:quote_B M Q o h (need k))(d:0≤b)(v:0≤a) (g:∀ i,0≤X i): Archive M k o h b a X Q:= ⟨0,Q,0,by simp,Rode.null g v,p,Rode.null g (by positivity),quote_none ..,u⟩
lemma Archive.pay₃ (p:Rode o (a*b^k) X Q)(d:0≤b)(v:0≤a) (g:∀ i,0≤X i): Archive M k o h b a X Q:= ⟨0,0,Q,by simp,Rode.null g v,Rode.null g (by positivity),p,quote_none ..,quote_none ..⟩
lemma Archive.scalar(v:Archive M k o h b a X Q)(z:ℝ):Archive M k o h b (‖z‖*a) X (z • Q):=by
 obtain ⟨U,V,R,w,f,l,e,t,h'⟩:=v.bill; exact ⟨z • U,z • V,z • R,by rw [w,smul_add,smul_add],f.scaleH z,by rw [mul_assoc]; exact l.scaleH z,by rw [mul_assoc]; exact e.scaleH z,quote_scale t z,quote_scale h' z⟩
end Boom
end YM.CF.TableF
end
