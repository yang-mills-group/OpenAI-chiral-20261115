import YM.SU5.FiniteGaugeData.Stent.Writ
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
variable {N P: Side}{L:Side}{R:Patch}
local notation "ℱ"=> FC (Single N)
universe u₀
-- support/fill all untouched. Tphase arbitrary over any finite fence
section
private lemma dleft {X₁ X₂:Type*}(f:X₁→X₂→ℂ)(r:Fin n→X₁)(s:Fin n→X₂)(h:(TaxR f r s).det≠0)(t:Equiv.Perm (Fin n)):(TaxR f (r ∘ t) s).det ≠0:=by
 change ((TaxR f r s).submatrix t id).det≠0; rw [Matrix.det_permute]; exact mul_ne_zero (by norm_cast; exact Units.ne_zero _) h
lemma reordered (r:Fin n→ X)(s:Fin n→Y₀)(h:(TaxR Trigo.levy r s).det≠0)(t u: Equiv.Perm (Fin n)): (TaxR Trigo.levy (r ∘ t) (s ∘ u)).det≠0:= by
 have hp:=dleft Trigo.levy r s h t; let v:= TaxR Trigo.levy (r ∘ t) s; change (v.submatrix id u).det ≠0; rw [Matrix.det_permute']; exact mul_ne_zero (by norm_cast; exact Units.ne_zero _) hp -- units?
abbrev registrant(b:Bool)(S:Finset Cover): Set (Trigo.Chamber b):= {a| nodeC a.1∈ S}
private lemma Press(F: Finset Cover)(b:Bool):(registrant b F).Finite:= ((F.finite_toSet.preimage nodeC_inj.injOn).prod (Set.finite_univ : (Set.univ:Set (Trigo.Spins b)).Finite)).subset (fun x h=>⟨h, Set.mem_univ _⟩) -- tune
abbrev Rack(b:Bool)(L:Finset Cover)(f: Fin n→ Trigo.Chamber b):Prop:= registrant b L ⊆ Set.range f
lemma Laug(x:X)(y:Y₀)(F: Finset Cover): ∃ (n:ℕ)(f:Fin (n+1)→ X)(g':Fin (n+1)→ Y₀),f 0=x ∧ g' 0=y ∧ Rack true F f ∧ Rack false F g'∧ (TaxR Trigo.levy f g').det ≠0:=by
 classical
 let g(b:Bool):=(Press F b).toFinset; obtain ⟨m,f,h,_,_,d,v,t⟩:= Trigo.augmented (insert x (g true)) (insert y (g false)); obtain ⟨i,he⟩:= v (by exact Finset.mem_insert_self x _); cases m with
 | zero=>exact i.elim0
 | succ m=> obtain ⟨j,u⟩:= t (by exact Finset.mem_insert_self y _); let p:=Equiv.swap (0:Fin (m+1)) i; let q:= Equiv.swap (0:Fin (m+1)) j; refine ⟨m,f ∘ p,h ∘ q,by rw [Function.comp_apply, show p 0=i from Equiv.swap_apply_left _ _,he],by rw [Function.comp_apply,show q 0=j from Equiv.swap_apply_left ..,u],fun a h=> ?_,fun a h=>?_, reordered f h d p q⟩
            · rw [p.surjective.range_comp]; exact v (by exact Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset ..).mpr h))
            rw [q.surjective.range_comp]; exact t (by exact Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset ..).mpr h))
#print axioms Laug
end
abbrev couture(N:Side){b:Bool}(f:Trigo.Chamber b): SU.Slot↪ Single N:=⟨fun i=> Lifted.index N f.1 f.2.val i,fun i j p=>congrArg Prod.snd p⟩
variable (F:Finset Cover)(vₚ: Hosp F N)
variable (f:Fin (n+1)→ X)(g':Fin (n+1)→Y₀)(h:Rack true F f)(t:Rack false F g')
include vₚ
section
include h
lemma lensH(i:Single N)(p:i∈ modesIn N (region F N))(e:i∈ Tset N)(u:i∉ (univ.map (couture N (f 0)))): ∃ (y:Fin n)(a:SU.Slot), (couture N (f y.succ)) a=i:=by
 obtain ⟨⟨⟨x,j,b⟩,hp⟩,rfl⟩:=occupy_surj F vₚ i p; change Lifted.index N x j b∈_ at e; have ht:j∈ Trigo.Spins true:=(grade_one ..).1 e; let w:X:=(x,⟨j,ht⟩); obtain ⟨s,hs⟩:= h (show w∈ _ from hp); change f s=w at hs
 refine Fin.cases ?_ ?_ s hs; · intro p; apply False.elim; apply u; rw [p]; exact mem_map.mpr ⟨b,mem_univ _,rfl⟩
 intro y p; refine ⟨y,b,?_⟩; rw [p]; rfl
omit h
include t
lemma lensL(i:Single N)(p:i∈ modesIn N (region F N))(e:i∈ (Tset N)ᶜ)(u:i∉ (univ.map (couture N (g' 0)))): ∃ (y:Fin n)(a:SU.Slot), (couture N (g' y.succ)) a=i:=by
 obtain ⟨⟨⟨x,j,b⟩,hp⟩,rfl⟩:=occupy_surj F vₚ i p; change Lifted.index N x j b∈_ at e; have ht:j∈ Trigo.Spins false:=(mem_compl.mpr (mt (grade_one (x:=wrap N x) j b).2 (mem_compl.mp e))); let w:Y₀:=(x,⟨j,ht⟩); obtain ⟨s,hs⟩:= t (show w∈ _ from hp); change g' s=w at hs
 refine Fin.cases ?_ ?_ s hs; · intro p; apply False.elim; apply u; rw [p]; exact mem_map.mpr ⟨b,mem_univ _,rfl⟩
 intro y p; refine ⟨y,b,?_⟩; rw [p]; rfl
#print axioms lensL
end
-- reduce kets exact mean.
local notation "W"=> TextK (f ∘ Fin.succ) (g' ∘ Fin.succ) N
omit vₚ
lemma RollSelf(x:Cover):‖Lifted.winding N x‖=1:= Rush.fee_norm _
lemma RollNz(x:Cover): Lifted.winding N x≠0:=norm_pos_iff.mp (by rw [RollSelf]; exact zero_lt_one)
variable {V:Ket (Single N)}
section
include vₚ h
lemma chiffonH (Z:withinM (modesIn N (region F N)) V)(p:withinM (Tset N) V):
   TextK (f ∘ Fin.succ) (g' ∘ Fin.succ) N * create V=W*(∑ i:SU.Slot, (V.ofLp ((couture N (f 0)) i) / Lifted.winding N (f 0).1) • create (quantum N (f 0) i)):=by
 let x:= f 0; let Q:= couture N x; let U(i:Single N):=W*(V.ofLp i • create (basisKet i)); let S:= univ.map Q; nth_rw 1 [← basis_expand V]; rw [map_sum]; simp_rw [map_smul,mul_sum]; change ∑ x:Single N,U x =_
 rw [← Finset.sum_subset (s₁:=S) (Finset.subset_univ _) ?_]; · rw [sum_map]; refine sum_congr rfl (fun i _=>?_); unfold quantum basisC; simp_rw [map_smul,smul_smul,div_mul_cancel₀ _ (RollNz _)]; rfl -- tune
 intro i _ u; by_cases d:i∈modesIn N (region F N); swap; · unfold U; rw [(within_test ..).mp Z i d]; simp
 by_cases l:i∈ Tset N; swap; · unfold U; rw [(within_test ..).mp p i l]; simp
 obtain ⟨s,a,w⟩:= lensH F vₚ f h i d l u; let x:= f s.succ; let i':= couture N x; let U₁ := TextK (f ∘ Fin.succ) (g' ∘ Fin.succ) N; have hz(x:X)(p:SU.Slot): create (quantum N x p)=Lifted.winding N x.1 • create (basisKet (couture N x p)):= map_smul ..; let T:= Lifted.winding N x.1; have hv:T • (W * create (basisKet i))=0:=by rw [←Algebra.mul_smul_comm,←w,←hz]; exact hanky ..
 unfold U; rw [Algebra.mul_smul_comm,(smul_eq_zero_iff_right (RollNz (N:=N) x.1)).1 hv,smul_zero]
#print axioms chiffonH
omit h
include t
lemma chiffonL (Z:withinM (modesIn N (region F N)) V)(p:withinM (Tset N)ᶜ V):
   TextK (f ∘ Fin.succ) (g' ∘ Fin.succ) N * Fock.remove V=W*(∑ i:SU.Slot, star (V.ofLp ((couture N (g' 0)) i) / Lifted.winding N (g' 0).1) • Fock.remove (quantum N (g' 0) i)):=by
 let x:= g' 0; let Q:= couture N x; let U(i:Single N):=W*(star (V.ofLp i) • star (create (basisKet i))); let S:= univ.map Q; unfold Fock.remove; nth_rw 1 [← basis_expand V]; rw [map_sum]; simp_rw [map_smul,star_sum,star_smul,mul_sum]; change ∑ i:Single N,U i =_
 rw [← Finset.sum_subset (s₁:=S) (Finset.subset_univ _) ?_]; · rw [sum_map]; refine sum_congr rfl (fun i _=>?_); unfold quantum basisC; simp_rw [map_smul,star_smul,smul_smul,star_div₀,div_mul_cancel₀ _ (by simpa using RollNz (N:=N) (g' 0).1 : star (Lifted.winding N (g' 0).1) ≠0)]; rfl -- star_div₀ maybe
 intro i _ u; by_cases d:i∈modesIn N (region F N); swap; · unfold U; rw [(within_test ..).mp Z i d]; simp
 by_cases l:i∈ (Tset N)ᶜ; swap; · unfold U; rw [(within_test ..).mp p i l]; simp
 obtain ⟨s,a,w⟩:= lensL F vₚ g' t i d l u; let x:= g' s.succ; let i':= couture N x; let U₁ := TextK (f ∘ Fin.succ) (g' ∘ Fin.succ) N; have hz(x:Y₀)(p:SU.Slot): Fock.remove (quantum N x p)=star (Lifted.winding N x.1) • star (create (basisKet (couture N x p))):=by unfold Fock.remove quantum basisC; rw [map_smul,star_smul]; rfl
 let T:= Lifted.winding N x.1; have hv:star T • (W * star (create (basisKet i)))=0:=by rw [←Algebra.mul_smul_comm,←w,←hz]; exact tiptoe ..
 unfold U; rw [Algebra.mul_smul_comm,(smul_eq_zero_iff_right (show star T≠0 from by simpa using RollNz (N:=N) x.1)).1 hv,smul_zero]
#print axioms chiffonL
end
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
