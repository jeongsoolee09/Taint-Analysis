from urllib.request import urlopen
from bs4 import BeautifulSoup


def scrape_class_names(url):
    html = urlopen(url)
    bs = BeautifulSoup(html, 'html.parser')
    class_names = []
    if 'java/lang' in url:
        for i in bs.find_all('a', {'title': 'class in java.lang'}):
            class_names.append(i.get_text())
    elif 'java/util' in url:
        for i in bs.find_all('a', {'title': 'class in java.util'}):
            class_names.append(i.get_text())
    return class_names
