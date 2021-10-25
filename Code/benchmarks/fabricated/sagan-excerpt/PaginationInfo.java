package sagan.support.nav;

import java.util.List;

/**
 * Used in views for rendering pagination controls. Note that page numbers are indexed
 * from 1 as opposed to 0.
 *
 * @see PageElement
 */


public class PaginationInfo {

  private class PageElementsBuilder {

    private long x;
    private long y;

    PageElementsBuilder(long a, long b) {
      this.x = a;
      this.y = b;
    }
  }
  private final long currentPage;
  private final long totalPages;

  public PaginationInfo() {
    currentPage = 1;
    totalPages = 2;
  }

  public boolean isVisible() {
    return isPreviousVisible() || isNextVisible();
  }

  public boolean isPreviousVisible() {
    return currentPage > 1;
  }

  public boolean isNextVisible() {
    return currentPage < totalPages;
  }

  public long getNextPageNumber() {
    return currentPage + 1;
  }

  public long getPreviousPageNumber() {
    return currentPage - 1;
  }

  public PageElementsBuilder getPageElements() {
    return new PageElementsBuilder(currentPage, totalPages);
  }

  @Override
  public boolean equals(Object o) {
    if (this == o)
      return true;
    if (o == null || getClass() != o.getClass())
      return false;

    PaginationInfo that = (PaginationInfo) o;

    if (currentPage != that.currentPage)
      return false;
    if (totalPages != that.totalPages)
      return false;

    return true;
  }

  @Override
  public int hashCode() {
    int result = (int) (currentPage ^ (currentPage >>> 32));
    result = 31 * result + (int) (totalPages ^ (totalPages >>> 32));
    return result;
  }
}
